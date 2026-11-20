//! IG-R harness ut_igr2 -- the GlobMatcher-verdict re-anchor unit
//! (the IG3 GlobSet-consumption seam, per the harness-inventory
//! section-6 plan: GL artifacts mounted by #[path] reference from the
//! sibling database/globset tree, no copies; the ignore twins' match
//! oracle stays untouched -- this unit proves the other side of the
//! per-instance admit seams).
//!
//! Scope: every DISTINCT (pattern, case-flag) pair the ut_ig3/ut_ig4/
//! ut_ig5 glob_pat_matches assume rows consume, at one true-valued and
//! one false-valued candidate where the rows provide both (the full
//! instance grid is 146 triples; the per-pair sampling below covers
//! every pattern family the rows touch -- the covered/remaining tally
//! sits in the IG-R batch notes).
//!
//! Chain per row (all machine-checked, zero assumes): GL2 parse on the
//! CALL-SITE options (two sites in play, chosen per admit-row
//! provenance: gitignore.rs:531-540 for the ut_ig3/ut_ig5 rows,
//! types.rs:341-343 -- literal_separator only, defaults elsewhere,
//! unclosed class off -- for the ut_ig4 typed-glob rows) -> GL4
//! strategy extraction (spec_match_strategy) -> the GL5/GL6 tier check
//! (spec_strat_check, GlobStrategic's is_match_candidate twin over the
//! token model). The runtime S8 mask columns measured the GlobMatcher
//! regex arm; the strategic-twin == regex-arm tie is the GL5 P6/GM10
//! boundary (the twotree rows pinned the sample geometries); a row
//! failing here would mean a genuine strategy-vs-regex divergence on
//! that instance, not a harness gap.
//! [IG-R batch status: PARKED as authored target-form; the full-unit
//! run is blocked by the GL2-era deep-composite compute wall -- the
//! star-composite parse shapes ('**/'-prefixed actuals are the bulk of
//! the instance domain) hang the ground compute rows at any rlimit
//! (probes p4a/p5b/p7/p10 of the IG-R batch; single-star and plain
//! shapes verified green, p9/p11/p12, and the short-domain anchor unit
//! ut_igr3 carries the green slice). The regeneration recipe for these
//! rows is the per-step SState ladder form over the GL2 mirror's state
//! trace (pit #IG-R-1); until then these rows stay authored but their
//! unit is not in the family sweep.]

use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::seq::seq;

#[path = "../../../globset/verified/src/lib.rs"]
mod glib;

#[allow(unused_imports)]
use glib::CowBytes;
#[allow(unused_imports)]
use glib::pathutil;

use glib::glob::{spec_match_strategy, spec_parse_glob, spec_strat_check};

verus! {

/// The char form's utf8 bytes: GL's own encode lane table folded over
/// the char sequence, prefix-style (the byte-tie carrier).
pub open spec fn igr_utf8_of_upto(cs: Seq<char>, i: nat) -> Seq<u8>
    decreases i
{
    if i == 0 {
        Seq::empty()
    } else {
        igr_utf8_of_upto(cs, (i - 1) as nat)
            + glib::glob::spec_utf8_encode(cs.index((i - 1) as int) as u32)
    }
}

/// The full fold.
pub open spec fn igr_utf8_of(cs: Seq<char>) -> Seq<u8> {
    igr_utf8_of_upto(cs, cs.len() as nat)
}

/// The gitignore call-site options (gitignore.rs:531-540: literal
/// separator, backslash escape, the builder's case flag and
/// unclosed-class toggle; empty alternates stay default).
pub open spec fn igr_opts_gitignore(ci: bool, auc: bool) -> glib::glob::GlobOptions {
    glib::glob::GlobOptions {
        case_insensitive: ci,
        literal_separator: true,
        backslash_escape: true,
        empty_alternates: false,
        allow_unclosed_class: auc,
    }
}

/// The types call-site options (types.rs:341-343: literal_separator
/// only -- every other flag rides the upstream default: case off,
/// unclosed class off; backslash escape is the platform default,
/// true on the unix oracle set).
pub open spec fn igr_opts_types() -> glib::glob::GlobOptions {
    glib::glob::GlobOptions {
        case_insensitive: false,
        literal_separator: true,
        backslash_escape: true,
        empty_alternates: false,
        allow_unclosed_class: false,
    }
}


/// Match seam instance (pattern '**', ci=false, candidate 'foo/bar', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m00_stst_t() {
    let cs = seq!['*', '*'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'o', 'o', '/', 'b', 'a', 'r'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'o', 'o', '/', 'b', 'a', 'r']) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72]) by (compute);
}


/// Match seam instance (pattern '**/!xy', ci=false, candidate '!xy', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m01_ststslexxy_t() {
    let cs = seq!['*', '*', '/', '!', 'x', 'y'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x21, 0x78, 0x79]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['!', 'x', 'y'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['!', 'x', 'y']) == seq![0x21, 0x78, 0x79]) by (compute);
}


/// Match seam instance (pattern '**/#foo', ci=false, candidate '#foo', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m02_ststslhafoo_t() {
    let cs = seq!['*', '*', '/', '#', 'f', 'o', 'o'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x23, 0x66, 0x6F, 0x6F]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['#', 'f', 'o', 'o'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['#', 'f', 'o', 'o']) == seq![0x23, 0x66, 0x6F, 0x6F]) by (compute);
}


/// Match seam instance (pattern '**/*', ci=false, candidate 'foo', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m03_ststslst_t() {
    let cs = seq!['*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'o', 'o'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'o', 'o']) == seq![0x66, 0x6F, 0x6F]) by (compute);
}


/// Match seam instance (pattern '**/**/*', ci=false, candidate 'a/foo.rs', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m04_ststslststslst_t() {
    let cs = seq!['*', '*', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['a', '/', 'f', 'o', 'o', '.', 'r', 's'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['a', '/', 'f', 'o', 'o', '.', 'r', 's']) == seq![0x61, 0x2F, 0x66, 0x6F, 0x6F, 0x2E, 0x72, 0x73]) by (compute);
}


/// Match seam instance (pattern '**/*.RS', ci=false, candidate 'x.RS', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m05_ststslstdtRS_t() {
    let cs = seq!['*', '*', '/', '*', '.', 'R', 'S'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x52, 0x53]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['x', '.', 'R', 'S'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['x', '.', 'R', 'S']) == seq![0x78, 0x2E, 0x52, 0x53]) by (compute);
}


/// Match seam instance (pattern '**/*.html', ci=false, candidate 'foo.html', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m06_ststslstdthtml_t() {
    let cs = seq!['*', '*', '/', '*', '.', 'h', 't', 'm', 'l'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'o', 'o', '.', 'h', 't', 'm', 'l'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'o', 'o', '.', 'h', 't', 'm', 'l']) == seq![0x66, 0x6F, 0x6F, 0x2E, 0x68, 0x74, 0x6D, 0x6C]) by (compute);
}


/// Match seam instance (pattern '**/*.html', ci=false, candidate 'foo.HTML', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m06_ststslstdthtml_f() {
    let cs = seq!['*', '*', '/', '*', '.', 'h', 't', 'm', 'l'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'o', 'o', '.', 'H', 'T', 'M', 'L'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'o', 'o', '.', 'H', 'T', 'M', 'L']) == seq![0x66, 0x6F, 0x6F, 0x2E, 0x48, 0x54, 0x4D, 0x4C]) by (compute);
}


/// Match seam instance (pattern '**/*.html', ci=true, candidate 'x.RS', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m07_ststslstdthtml_f() {
    let cs = seq!['*', '*', '/', '*', '.', 'h', 't', 'm', 'l'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C]) by (compute);
    let opts = igr_opts_gitignore(true, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['x', '.', 'R', 'S'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['x', '.', 'R', 'S']) == seq![0x78, 0x2E, 0x52, 0x53]) by (compute);
}


/// Match seam instance (pattern '**/*.lock', ci=false, candidate 'Cargo.lock', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m08_ststslstdtlock_t() {
    let cs = seq!['*', '*', '/', '*', '.', 'l', 'o', 'c', 'k'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x6C, 0x6F, 0x63, 0x6B]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['C', 'a', 'r', 'g', 'o', '.', 'l', 'o', 'c', 'k'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['C', 'a', 'r', 'g', 'o', '.', 'l', 'o', 'c', 'k']) == seq![0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63, 0x6B]) by (compute);
}


/// Match seam instance (pattern '**/*.rs', ci=false, candidate 'src/main.rs', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m09_ststslstdtrs_t() {
    let cs = seq!['*', '*', '/', '*', '.', 'r', 's'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x72, 0x73]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['s', 'r', 'c', '/', 'm', 'a', 'i', 'n', '.', 'r', 's'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['s', 'r', 'c', '/', 'm', 'a', 'i', 'n', '.', 'r', 's']) == seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]) by (compute);
}


/// Match seam instance (pattern '**/.hid', ci=false, candidate '.hid', verdict true):
/// the admit row gstrip_p5t3 in ut_ig5.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m10_ststsldthid_t() {
    let cs = seq!['*', '*', '/', '.', 'h', 'i', 'd'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2E, 0x68, 0x69, 0x64]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['.', 'h', 'i', 'd'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['.', 'h', 'i', 'd']) == seq![0x2E, 0x68, 0x69, 0x64]) by (compute);
}


/// Match seam instance (pattern '**/Cargo.lock', ci=false, candidate 'tabwriter-bin/Cargo.lock', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m11_ststslCargodtlock_t() {
    let cs = seq!['*', '*', '/', 'C', 'a', 'r', 'g', 'o', '.', 'l', 'o', 'c', 'k'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63, 0x6B]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['t', 'a', 'b', 'w', 'r', 'i', 't', 'e', 'r', '-', 'b', 'i', 'n', '/', 'C', 'a', 'r', 'g', 'o', '.', 'l', 'o', 'c', 'k'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['t', 'a', 'b', 'w', 'r', 'i', 't', 'e', 'r', '-', 'b', 'i', 'n', '/', 'C', 'a', 'r', 'g', 'o', '.', 'l', 'o', 'c', 'k']) == seq![0x74, 0x61, 0x62, 0x77, 0x72, 0x69, 0x74, 0x65, 0x72, 0x2D, 0x62, 0x69, 0x6E, 0x2F, 0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63, 0x6B]) by (compute);
}


/// Match seam instance (pattern '**/amonths', ci=false, candidate 'months', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m12_ststslamonths_f() {
    let cs = seq!['*', '*', '/', 'a', 'm', 'o', 'n', 't', 'h', 's'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['m', 'o', 'n', 't', 'h', 's'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['m', 'o', 'n', 't', 'h', 's']) == seq![0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]) by (compute);
}


/// Match seam instance (pattern '**/bar', ci=false, candidate 'bar', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m13_ststslbar_t() {
    let cs = seq!['*', '*', '/', 'b', 'a', 'r'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['b', 'a', 'r'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['b', 'a', 'r']) == seq![0x62, 0x61, 0x72]) by (compute);
}


/// Match seam instance (pattern '**/bar', ci=false, candidate '/home/foobar', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m13_ststslbar_f() {
    let cs = seq!['*', '*', '/', 'b', 'a', 'r'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['/', 'h', 'o', 'm', 'e', '/', 'f', 'o', 'o', 'b', 'a', 'r'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['/', 'h', 'o', 'm', 'e', '/', 'f', 'o', 'o', 'b', 'a', 'r']) == seq![0x2F, 0x68, 0x6F, 0x6D, 0x65, 0x2F, 0x66, 0x6F, 0x6F, 0x62, 0x61, 0x72]) by (compute);
}


/// Match seam instance (pattern '**/baz', ci=false, candidate 'baz', verdict true):
/// the admit row gstrip_p5t3 in ut_ig5.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m14_ststslbaz_t() {
    let cs = seq!['*', '*', '/', 'b', 'a', 'z'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x7A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['b', 'a', 'z'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['b', 'a', 'z']) == seq![0x62, 0x61, 0x7A]) by (compute);
}


/// Match seam instance (pattern '**/baz', ci=false, candidate 'foo', verdict false):
/// the admit row gstrip_p5t3 in ut_ig5.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m14_ststslbaz_f() {
    let cs = seq!['*', '*', '/', 'b', 'a', 'z'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x7A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'o', 'o'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'o', 'o']) == seq![0x66, 0x6F, 0x6F]) by (compute);
}


/// Match seam instance (pattern '**/file_deep_01', ci=false, candidate 'parent_dir/file_deep_01', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m15_ststslfilec5fdeepc5f01_f() {
    let cs = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '0', '1'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x31]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '0', '1'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '0', '1']) == seq![0x70, 0x61, 0x72, 0x65, 0x6E, 0x74, 0x5F, 0x64, 0x69, 0x72, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x31]) by (compute);
}


/// Match seam instance (pattern '**/file_deep_31', ci=false, candidate 'parent_dir/file_deep_31', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m16_ststslfilec5fdeepc5f31_f() {
    let cs = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '3', '1'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x31]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '3', '1'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '3', '1']) == seq![0x70, 0x61, 0x72, 0x65, 0x6E, 0x74, 0x5F, 0x64, 0x69, 0x72, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x31]) by (compute);
}


/// Match seam instance (pattern '**/file_deep_32/*', ci=false, candidate 'parent_dir/file_deep_32', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m17_ststslfilec5fdeepc5f32slst_f() {
    let cs = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '3', '2', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x32, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '3', '2'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '3', '2']) == seq![0x70, 0x61, 0x72, 0x65, 0x6E, 0x74, 0x5F, 0x64, 0x69, 0x72, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x32]) by (compute);
}


/// Match seam instance (pattern '**/file_deep_33/**/*', ci=false, candidate 'parent_dir/file_deep_33', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m18_ststslfilec5fdeepc5f33slst_f() {
    let cs = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '3', '3', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '3', '3'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '3', '3']) == seq![0x70, 0x61, 0x72, 0x65, 0x6E, 0x74, 0x5F, 0x64, 0x69, 0x72, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x33]) by (compute);
}


/// Match seam instance (pattern '**/file_root_00', ci=false, candidate 'file_root_00', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m19_ststslfilec5frootc5f00_t() {
    let cs = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '0'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x30]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '0'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '0']) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x30]) by (compute);
}


/// Match seam instance (pattern '**/file_root_00', ci=false, candidate '', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m19_ststslfilec5frootc5f00_f() {
    let cs = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '0'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x30]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq![],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq![]) == seq![]) by (compute);
}


/// Match seam instance (pattern '**/file_root_01', ci=false, candidate 'file_root_01', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m20_ststslfilec5frootc5f01_f() {
    let cs = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '1'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x31]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '1'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '1']) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x31]) by (compute);
}


/// Match seam instance (pattern '**/file_root_31', ci=false, candidate 'file_root_31', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m21_ststslfilec5frootc5f31_f() {
    let cs = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '3', '1'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x31]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '3', '1'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '3', '1']) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x31]) by (compute);
}


/// Match seam instance (pattern '**/file_root_32/*', ci=false, candidate 'file_root_32', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m22_ststslfilec5frootc5f32slst_f() {
    let cs = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '3', '2', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x32, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '3', '2'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '3', '2']) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x32]) by (compute);
}


/// Match seam instance (pattern '**/file_root_33/**/*', ci=false, candidate 'file_root_33', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m23_ststslfilec5frootc5f33slst_f() {
    let cs = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '3', '3', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '3', '3'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '3', '3']) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x33]) by (compute);
}


/// Match seam instance (pattern '**/foo', ci=false, candidate 'foo', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m24_ststslfoo_t() {
    let cs = seq!['*', '*', '/', 'f', 'o', 'o'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'o', 'o'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'o', 'o']) == seq![0x66, 0x6F, 0x6F]) by (compute);
}


/// Match seam instance (pattern '**/foo', ci=false, candidate 'bar', verdict false):
/// the admit row gstrip_p5t3 in ut_ig5.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m24_ststslfoo_f() {
    let cs = seq!['*', '*', '/', 'f', 'o', 'o'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['b', 'a', 'r'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['b', 'a', 'r']) == seq![0x62, 0x61, 0x72]) by (compute);
}


/// Match seam instance (pattern '**/foo/**/*', ci=false, candidate 'src/foo/bar', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m25_ststslfooslststslst_t() {
    let cs = seq!['*', '*', '/', 'f', 'o', 'o', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['s', 'r', 'c', '/', 'f', 'o', 'o', '/', 'b', 'a', 'r'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['s', 'r', 'c', '/', 'f', 'o', 'o', '/', 'b', 'a', 'r']) == seq![0x73, 0x72, 0x63, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72]) by (compute);
}


/// Match seam instance (pattern '**/foo/**/*', ci=false, candidate 'wat/src/afoo/bar/baz', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m25_ststslfooslststslst_f() {
    let cs = seq!['*', '*', '/', 'f', 'o', 'o', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['w', 'a', 't', '/', 's', 'r', 'c', '/', 'a', 'f', 'o', 'o', '/', 'b', 'a', 'r', '/', 'b', 'a', 'z'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['w', 'a', 't', '/', 's', 'r', 'c', '/', 'a', 'f', 'o', 'o', '/', 'b', 'a', 'r', '/', 'b', 'a', 'z']) == seq![0x77, 0x61, 0x74, 0x2F, 0x73, 0x72, 0x63, 0x2F, 0x61, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A]) by (compute);
}


/// Match seam instance (pattern '**/foo/bar', ci=false, candidate 'foo/bar', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m26_ststslfooslbar_t() {
    let cs = seq!['*', '*', '/', 'f', 'o', 'o', '/', 'b', 'a', 'r'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'o', 'o', '/', 'b', 'a', 'r'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'o', 'o', '/', 'b', 'a', 'r']) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72]) by (compute);
}


/// Match seam instance (pattern '**/foo/bar', ci=false, candidate 'foo/src/bar', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m26_ststslfooslbar_f() {
    let cs = seq!['*', '*', '/', 'f', 'o', 'o', '/', 'b', 'a', 'r'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'o', 'o', '/', 's', 'r', 'c', '/', 'b', 'a', 'r'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'o', 'o', '/', 's', 'r', 'c', '/', 'b', 'a', 'r']) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x73, 0x72, 0x63, 0x2F, 0x62, 0x61, 0x72]) by (compute);
}


/// Match seam instance (pattern '**/months', ci=false, candidate 'months', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m27_ststslmonths_t() {
    let cs = seq!['*', '*', '/', 'm', 'o', 'n', 't', 'h', 's'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['m', 'o', 'n', 't', 'h', 's'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['m', 'o', 'n', 't', 'h', 's']) == seq![0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]) by (compute);
}


/// Match seam instance (pattern '**/monthsa', ci=false, candidate 'months', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m28_ststslmonthsa_f() {
    let cs = seq!['*', '*', '/', 'm', 'o', 'n', 't', 'h', 's', 'a'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73, 0x61]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['m', 'o', 'n', 't', 'h', 's'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['m', 'o', 'n', 't', 'h', 's']) == seq![0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]) by (compute);
}


/// Match seam instance (pattern '**/node_modules', ci=false, candidate 'node_modules', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m29_ststslnodec5fmodules_t() {
    let cs = seq!['*', '*', '/', 'n', 'o', 'd', 'e', '_', 'm', 'o', 'd', 'u', 'l', 'e', 's'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['n', 'o', 'd', 'e', '_', 'm', 'o', 'd', 'u', 'l', 'e', 's'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['n', 'o', 'd', 'e', '_', 'm', 'o', 'd', 'u', 'l', 'e', 's']) == seq![0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73]) by (compute);
}


/// Match seam instance (pattern '**/s*.rs', ci=false, candidate 'sfoo.rs', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m30_ststslsstdtrs_t() {
    let cs = seq!['*', '*', '/', 's', '*', '.', 'r', 's'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x73, 0x2A, 0x2E, 0x72, 0x73]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['s', 'f', 'o', 'o', '.', 'r', 's'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['s', 'f', 'o', 'o', '.', 'r', 's']) == seq![0x73, 0x66, 0x6F, 0x6F, 0x2E, 0x72, 0x73]) by (compute);
}


/// Match seam instance (pattern '**/s*.rs', ci=false, candidate 'src/foo.rs', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m30_ststslsstdtrs_f() {
    let cs = seq!['*', '*', '/', 's', '*', '.', 'r', 's'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x73, 0x2A, 0x2E, 0x72, 0x73]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['s', 'r', 'c', '/', 'f', 'o', 'o', '.', 'r', 's'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['s', 'r', 'c', '/', 'f', 'o', 'o', '.', 'r', 's']) == seq![0x73, 0x72, 0x63, 0x2F, 0x66, 0x6F, 0x6F, 0x2E, 0x72, 0x73]) by (compute);
}


/// Match seam instance (pattern '**/target', ci=false, candidate 'grep/target', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m31_ststsltarget_t() {
    let cs = seq!['*', '*', '/', 't', 'a', 'r', 'g', 'e', 't'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x74, 0x61, 0x72, 0x67, 0x65, 0x74]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['g', 'r', 'e', 'p', '/', 't', 'a', 'r', 'g', 'e', 't'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['g', 'r', 'e', 'p', '/', 't', 'a', 'r', 'g', 'e', 't']) == seq![0x67, 0x72, 0x65, 0x70, 0x2F, 0x74, 0x61, 0x72, 0x67, 0x65, 0x74]) by (compute);
}


/// Match seam instance (pattern '**/zzgood', ci=false, candidate 'zzgood', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m32_ststslzzgood_t() {
    let cs = seq!['*', '*', '/', 'z', 'z', 'g', 'o', 'o', 'd'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['z', 'z', 'g', 'o', 'o', 'd'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['z', 'z', 'g', 'o', 'o', 'd']) == seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64]) by (compute);
}


/// Match seam instance (pattern '**/zzgood', ci=false, candidate 'postgood', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m32_ststslzzgood_f() {
    let cs = seq!['*', '*', '/', 'z', 'z', 'g', 'o', 'o', 'd'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'o', 's', 't', 'g', 'o', 'o', 'd'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'o', 's', 't', 'g', 'o', 'o', 'd']) == seq![0x70, 0x6F, 0x73, 0x74, 0x67, 0x6F, 0x6F, 0x64]) by (compute);
}


/// Match seam instance (pattern '*.c', ci=false, candidate 'cat-file.c', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m33_stdtc_t() {
    let cs = seq!['*', '.', 'c'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2E, 0x63]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['c', 'a', 't', '-', 'f', 'i', 'l', 'e', '.', 'c'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['c', 'a', 't', '-', 'f', 'i', 'l', 'e', '.', 'c']) == seq![0x63, 0x61, 0x74, 0x2D, 0x66, 0x69, 0x6C, 0x65, 0x2E, 0x63]) by (compute);
}


/// Match seam instance (pattern '*.c', ci=false, candidate 'mozilla-sha1/sha1.c', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m33_stdtc_f() {
    let cs = seq!['*', '.', 'c'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2E, 0x63]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['m', 'o', 'z', 'i', 'l', 'l', 'a', '-', 's', 'h', 'a', '1', '/', 's', 'h', 'a', '1', '.', 'c'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['m', 'o', 'z', 'i', 'l', 'l', 'a', '-', 's', 'h', 'a', '1', '/', 's', 'h', 'a', '1', '.', 'c']) == seq![0x6D, 0x6F, 0x7A, 0x69, 0x6C, 0x6C, 0x61, 0x2D, 0x73, 0x68, 0x61, 0x31, 0x2F, 0x73, 0x68, 0x61, 0x31, 0x2E, 0x63]) by (compute);
}


/// Match seam instance (pattern '*.log', ci=false, candidate 'x.log', verdict true):
/// the admit row gstrip_p5t3 in ut_ig5.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m34_stdtlog_t() {
    let cs = seq!['*', '.', 'l', 'o', 'g'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2E, 0x6C, 0x6F, 0x67]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['x', '.', 'l', 'o', 'g'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['x', '.', 'l', 'o', 'g']) == seq![0x78, 0x2E, 0x6C, 0x6F, 0x67]) by (compute);
}


/// Match seam instance (pattern '*.log', ci=false, candidate 'baz', verdict false):
/// the admit row gstrip_p5t3 in ut_ig5.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m34_stdtlog_f() {
    let cs = seq!['*', '.', 'l', 'o', 'g'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2E, 0x6C, 0x6F, 0x67]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['b', 'a', 'z'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['b', 'a', 'z']) == seq![0x62, 0x61, 0x7A]) by (compute);
}


/// Match seam instance (pattern '*.rs', ci=false, candidate 'lib.rs', verdict true):
/// the admit row ? in ut_ig4.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m35_stdtrs_t() {
    let cs = seq!['*', '.', 'r', 's'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2E, 0x72, 0x73]) by (compute);
    let opts = igr_opts_types();
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['l', 'i', 'b', '.', 'r', 's'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['l', 'i', 'b', '.', 'r', 's']) == seq![0x6C, 0x69, 0x62, 0x2E, 0x72, 0x73]) by (compute);
}


/// Match seam instance (pattern '*.rs', ci=false, candidate 'index.html', verdict false):
/// the admit row ? in ut_ig4.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m35_stdtrs_f() {
    let cs = seq!['*', '.', 'r', 's'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2E, 0x72, 0x73]) by (compute);
    let opts = igr_opts_types();
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['i', 'n', 'd', 'e', 'x', '.', 'h', 't', 'm', 'l'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['i', 'n', 'd', 'e', 'x', '.', 'h', 't', 'm', 'l']) == seq![0x69, 0x6E, 0x64, 0x65, 0x78, 0x2E, 0x68, 0x74, 0x6D, 0x6C]) by (compute);
}


/// Match seam instance (pattern '*/file_deep_21', ci=false, candidate 'parent_dir/file_deep_21', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m36_stslfilec5fdeepc5f21_f() {
    let cs = seq!['*', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '2', '1'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x31]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '2', '1'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '2', '1']) == seq![0x70, 0x61, 0x72, 0x65, 0x6E, 0x74, 0x5F, 0x64, 0x69, 0x72, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x31]) by (compute);
}


/// Match seam instance (pattern '*/file_deep_22/*', ci=false, candidate 'parent_dir/file_deep_22', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m37_stslfilec5fdeepc5f22slst_f() {
    let cs = seq!['*', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '2', '2', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x32, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '2', '2'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '2', '2']) == seq![0x70, 0x61, 0x72, 0x65, 0x6E, 0x74, 0x5F, 0x64, 0x69, 0x72, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x32]) by (compute);
}


/// Match seam instance (pattern '*/file_deep_23/**/*', ci=false, candidate 'parent_dir/file_deep_23', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m38_stslfilec5fdeepc5f23slstst_f() {
    let cs = seq!['*', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '2', '3', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '2', '3'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '2', '3']) == seq![0x70, 0x61, 0x72, 0x65, 0x6E, 0x74, 0x5F, 0x64, 0x69, 0x72, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x33]) by (compute);
}


/// Match seam instance (pattern '*/file_root_20', ci=false, candidate 'file_root_20', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m39_stslfilec5frootc5f20_f() {
    let cs = seq!['*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '0'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x30]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '0'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '0']) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x30]) by (compute);
}


/// Match seam instance (pattern '*/file_root_21', ci=false, candidate 'file_root_21', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m40_stslfilec5frootc5f21_f() {
    let cs = seq!['*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '1'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x31]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '1'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '1']) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x31]) by (compute);
}


/// Match seam instance (pattern '*/file_root_22/*', ci=false, candidate 'file_root_22', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m41_stslfilec5frootc5f22slst_f() {
    let cs = seq!['*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '2', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x32, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '2'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '2']) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x32]) by (compute);
}


/// Match seam instance (pattern '*/file_root_23/**/*', ci=false, candidate 'file_root_23', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m42_stslfilec5frootc5f23slstst_f() {
    let cs = seq!['*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '3', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '3'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '3']) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x33]) by (compute);
}


/// Match seam instance (pattern '.a/b', ci=false, candidate '.a/b', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m43_dtaslb_t() {
    let cs = seq!['.', 'a', '/', 'b'];
    assert(igr_utf8_of(cs) == seq![0x2E, 0x61, 0x2F, 0x62]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['.', 'a', '/', 'b'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['.', 'a', '/', 'b']) == seq![0x2E, 0x61, 0x2F, 0x62]) by (compute);
}


/// Match seam instance (pattern 'a/**/b', ci=false, candidate 'a/b', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m44_aslststslb_t() {
    let cs = seq!['a', '/', '*', '*', '/', 'b'];
    assert(igr_utf8_of(cs) == seq![0x61, 0x2F, 0x2A, 0x2A, 0x2F, 0x62]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['a', '/', 'b'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['a', '/', 'b']) == seq![0x61, 0x2F, 0x62]) by (compute);
}


/// Match seam instance (pattern 'abc/**/*', ci=false, candidate 'abc/x', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m45_abcslststslst_t() {
    let cs = seq!['a', 'b', 'c', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x61, 0x62, 0x63, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['a', 'b', 'c', '/', 'x'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['a', 'b', 'c', '/', 'x']) == seq![0x61, 0x62, 0x63, 0x2F, 0x78]) by (compute);
}


/// Match seam instance (pattern 'bar', ci=false, candidate 'foo/bar', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m46_bar_f() {
    let cs = seq!['b', 'a', 'r'];
    assert(igr_utf8_of(cs) == seq![0x62, 0x61, 0x72]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'o', 'o', '/', 'b', 'a', 'r'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'o', 'o', '/', 'b', 'a', 'r']) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72]) by (compute);
}


/// Match seam instance (pattern 'file_deep_02/*', ci=false, candidate 'parent_dir/file_deep_02', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m47_filec5fdeepc5f02slst_f() {
    let cs = seq!['f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '0', '2', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x32, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '0', '2'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '0', '2']) == seq![0x70, 0x61, 0x72, 0x65, 0x6E, 0x74, 0x5F, 0x64, 0x69, 0x72, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x32]) by (compute);
}


/// Match seam instance (pattern 'file_deep_03/**/*', ci=false, candidate 'parent_dir/file_deep_03', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m48_filec5fdeepc5f03slststslst_f() {
    let cs = seq!['f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '0', '3', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '0', '3'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '0', '3']) == seq![0x70, 0x61, 0x72, 0x65, 0x6E, 0x74, 0x5F, 0x64, 0x69, 0x72, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x33]) by (compute);
}


/// Match seam instance (pattern 'file_deep_10', ci=false, candidate 'parent_dir/file_deep_10', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m49_filec5fdeepc5f10_f() {
    let cs = seq!['f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '0'];
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x30]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '0'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '0']) == seq![0x70, 0x61, 0x72, 0x65, 0x6E, 0x74, 0x5F, 0x64, 0x69, 0x72, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x30]) by (compute);
}


/// Match seam instance (pattern 'file_deep_11', ci=false, candidate 'parent_dir/file_deep_11', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m50_filec5fdeepc5f11_f() {
    let cs = seq!['f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '1'];
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x31]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '1'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '1']) == seq![0x70, 0x61, 0x72, 0x65, 0x6E, 0x74, 0x5F, 0x64, 0x69, 0x72, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x31]) by (compute);
}


/// Match seam instance (pattern 'file_deep_12/*', ci=false, candidate 'parent_dir/file_deep_12', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m51_filec5fdeepc5f12slst_f() {
    let cs = seq!['f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '2', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x32, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '2'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '2']) == seq![0x70, 0x61, 0x72, 0x65, 0x6E, 0x74, 0x5F, 0x64, 0x69, 0x72, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x32]) by (compute);
}


/// Match seam instance (pattern 'file_deep_13/**/*', ci=false, candidate 'parent_dir/file_deep_13', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m52_filec5fdeepc5f13slststslst_f() {
    let cs = seq!['f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '3', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '3'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 'r', 'e', 'n', 't', '_', 'd', 'i', 'r', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '3']) == seq![0x70, 0x61, 0x72, 0x65, 0x6E, 0x74, 0x5F, 0x64, 0x69, 0x72, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x33]) by (compute);
}


/// Match seam instance (pattern 'file_root_02/*', ci=false, candidate 'file_root_02', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m53_filec5frootc5f02slst_f() {
    let cs = seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '2', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x32, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '2'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '2']) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x32]) by (compute);
}


/// Match seam instance (pattern 'file_root_03/**/*', ci=false, candidate 'file_root_03', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m54_filec5frootc5f03slststslst_f() {
    let cs = seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '3', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '3'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '3']) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x33]) by (compute);
}


/// Match seam instance (pattern 'file_root_11', ci=false, candidate 'file_root_11', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m55_filec5frootc5f11_f() {
    let cs = seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '1', '1'];
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x31]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '1', '1'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '1', '1']) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x31]) by (compute);
}


/// Match seam instance (pattern 'file_root_12/*', ci=false, candidate 'file_root_12', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m56_filec5frootc5f12slst_f() {
    let cs = seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '1', '2', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x32, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '1', '2'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '1', '2']) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x32]) by (compute);
}


/// Match seam instance (pattern 'file_root_13/**/*', ci=false, candidate 'file_root_13', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m57_filec5frootc5f13slststslst_f() {
    let cs = seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '1', '3', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '1', '3'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '1', '3']) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x33]) by (compute);
}


/// Match seam instance (pattern 'foo', ci=false, candidate 'x/y/bar', verdict false):
/// the admit row gstrip_p5t3 in ut_ig5.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m58_foo_f() {
    let cs = seq!['f', 'o', 'o'];
    assert(igr_utf8_of(cs) == seq![0x66, 0x6F, 0x6F]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['x', '/', 'y', '/', 'b', 'a', 'r'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['x', '/', 'y', '/', 'b', 'a', 'r']) == seq![0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72]) by (compute);
}


/// Match seam instance (pattern 'foo/**/*', ci=false, candidate 'foo', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m59_fooslststslst_f() {
    let cs = seq!['f', 'o', 'o', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'o', 'o'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'o', 'o']) == seq![0x66, 0x6F, 0x6F]) by (compute);
}


/// Match seam instance (pattern 'foo/bar/baz', ci=false, candidate 'foo/bar/baz', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m60_fooslbarslbaz_t() {
    let cs = seq!['f', 'o', 'o', '/', 'b', 'a', 'r', '/', 'b', 'a', 'z'];
    assert(igr_utf8_of(cs) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'o', 'o', '/', 'b', 'a', 'r', '/', 'b', 'a', 'z'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'o', 'o', '/', 'b', 'a', 'r', '/', 'b', 'a', 'z']) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A]) by (compute);
}


/// Match seam instance (pattern 'llvm', ci=false, candidate 'llvm', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m61_llvm_t() {
    let cs = seq!['l', 'l', 'v', 'm'];
    assert(igr_utf8_of(cs) == seq![0x6C, 0x6C, 0x76, 0x6D]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['l', 'l', 'v', 'm'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['l', 'l', 'v', 'm']) == seq![0x6C, 0x6C, 0x76, 0x6D]) by (compute);
}


/// Match seam instance (pattern 'm4/ltoptions.m4', ci=false, candidate 'csharp/src/packages/repositories.config', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m62_m4slltoptionsdtm4_f() {
    let cs = seq!['m', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'];
    assert(igr_utf8_of(cs) == seq![0x6D, 0x34, 0x2F, 0x6C, 0x74, 0x6F, 0x70, 0x74, 0x69, 0x6F, 0x6E, 0x73, 0x2E, 0x6D, 0x34]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['c', 's', 'h', 'a', 'r', 'p', '/', 's', 'r', 'c', '/', 'p', 'a', 'c', 'k', 'a', 'g', 'e', 's', '/', 'r', 'e', 'p', 'o', 's', 'i', 't', 'o', 'r', 'i', 'e', 's', '.', 'c', 'o', 'n', 'f', 'i', 'g'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['c', 's', 'h', 'a', 'r', 'p', '/', 's', 'r', 'c', '/', 'p', 'a', 'c', 'k', 'a', 'g', 'e', 's', '/', 'r', 'e', 'p', 'o', 's', 'i', 't', 'o', 'r', 'i', 'e', 's', '.', 'c', 'o', 'n', 'f', 'i', 'g']) == seq![0x63, 0x73, 0x68, 0x61, 0x72, 0x70, 0x2F, 0x73, 0x72, 0x63, 0x2F, 0x70, 0x61, 0x63, 0x6B, 0x61, 0x67, 0x65, 0x73, 0x2F, 0x72, 0x65, 0x70, 0x6F, 0x73, 0x69, 0x74, 0x6F, 0x72, 0x69, 0x65, 0x73, 0x2E, 0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67]) by (compute);
}


/// Match seam instance (pattern 'path1/*', ci=false, candidate 'path1/foo', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m63_path1slst_t() {
    let cs = seq!['p', 'a', 't', 'h', '1', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x70, 0x61, 0x74, 0x68, 0x31, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 't', 'h', '1', '/', 'f', 'o', 'o'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 't', 'h', '1', '/', 'f', 'o', 'o']) == seq![0x70, 0x61, 0x74, 0x68, 0x31, 0x2F, 0x66, 0x6F, 0x6F]) by (compute);
}


/// Match seam instance (pattern 'path1/*', ci=false, candidate 'path2/path1/foo', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m63_path1slst_f() {
    let cs = seq!['p', 'a', 't', 'h', '1', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x70, 0x61, 0x74, 0x68, 0x31, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['p', 'a', 't', 'h', '2', '/', 'p', 'a', 't', 'h', '1', '/', 'f', 'o', 'o'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['p', 'a', 't', 'h', '2', '/', 'p', 'a', 't', 'h', '1', '/', 'f', 'o', 'o']) == seq![0x70, 0x61, 0x74, 0x68, 0x32, 0x2F, 0x70, 0x61, 0x74, 0x68, 0x31, 0x2F, 0x66, 0x6F, 0x6F]) by (compute);
}


/// Match seam instance (pattern 'src/*.rs', ci=false, candidate 'src/main.rs', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m64_srcslstdtrs_t() {
    let cs = seq!['s', 'r', 'c', '/', '*', '.', 'r', 's'];
    assert(igr_utf8_of(cs) == seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['s', 'r', 'c', '/', 'm', 'a', 'i', 'n', '.', 'r', 's'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['s', 'r', 'c', '/', 'm', 'a', 'i', 'n', '.', 'r', 's']) == seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]) by (compute);
}


/// Match seam instance (pattern 'src/*.rs', ci=false, candidate 'src/grep/src/main.rs', verdict false):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m64_srcslstdtrs_f() {
    let cs = seq!['s', 'r', 'c', '/', '*', '.', 'r', 's'];
    assert(igr_utf8_of(cs) == seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['s', 'r', 'c', '/', 'g', 'r', 'e', 'p', '/', 's', 'r', 'c', '/', 'm', 'a', 'i', 'n', '.', 'r', 's'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['s', 'r', 'c', '/', 'g', 'r', 'e', 'p', '/', 's', 'r', 'c', '/', 'm', 'a', 'i', 'n', '.', 'r', 's']) == seq![0x73, 0x72, 0x63, 0x2F, 0x67, 0x72, 0x65, 0x70, 0x2F, 0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]) by (compute);
}


/// Match seam instance (pattern 'src/main.rs', ci=false, candidate 'src/main.rs', verdict true):
/// the admit row ? in ut_ig3.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m65_srcslmaindtrs_t() {
    let cs = seq!['s', 'r', 'c', '/', 'm', 'a', 'i', 'n', '.', 'r', 's'];
    assert(igr_utf8_of(cs) == seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['s', 'r', 'c', '/', 'm', 'a', 'i', 'n', '.', 'r', 's'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['s', 'r', 'c', '/', 'm', 'a', 'i', 'n', '.', 'r', 's']) == seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]) by (compute);
}


/// Match seam instance (pattern 'sub/**/*', ci=false, candidate 'sub/x', verdict true):
/// the admit row gstrip_p5t3 in ut_ig5.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m66_subslststslst_t() {
    let cs = seq!['s', 'u', 'b', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['s', 'u', 'b', '/', 'x'],
        64,
    ) == true) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['s', 'u', 'b', '/', 'x']) == seq![0x73, 0x75, 0x62, 0x2F, 0x78]) by (compute);
}


/// Match seam instance (pattern 'sub/**/*', ci=false, candidate 'foo/x.log', verdict false):
/// the admit row gstrip_p5t3 in ut_ig5.rs pins the oracle; the GL chain below
/// reproduces the verdict on the same instance.
proof fn igr_m66_subslststslst_f() {
    let cs = seq!['s', 'u', 'b', '/', '*', '*', '/', '*'];
    assert(igr_utf8_of(cs) == seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]) by (compute);
    let opts = igr_opts_gitignore(false, true);
    let r = spec_parse_glob(cs, opts, false);
    assert(r is Ok) by (compute);
    let ts = r.get_Ok_0();
    let strat = spec_match_strategy(opts, ts, 24);
    assert(spec_strat_check(
        opts,
        strat,
        ts,
        seq!['f', 'o', 'o', '/', 'x', '.', 'l', 'o', 'g'],
        64,
    ) == false) by (compute);
    // candidate byte tie (the admit row's candidate literal)
    assert(igr_utf8_of(seq!['f', 'o', 'o', '/', 'x', '.', 'l', 'o', 'g']) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x78, 0x2E, 0x6C, 0x6F, 0x67]) by (compute);
}


} // verus!

fn main() {}
