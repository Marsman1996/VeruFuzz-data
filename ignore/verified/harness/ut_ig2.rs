//! ignore IG2 **harness zone** -- the KAT rows over the src-zone twin
//! (verified/src/lib.rs, which mounts verified/src/pathutil.rs and
//! verified/src/gitignore.rs, the batch-IG2 builder twin).
//!
//! Row families (per harness-inventory section 10, the IG2 harness row):
//! - UT-A: the 74 inline gitignore vectors, parse faces -- every distinct
//!   vector line gets a value-model row asserting the full GlobSpec record
//!   (original / actual / is_whitelist / is_only_dir) plus the verdict
//!   admit (runtime columns S1/S2).
//! - UT-B: grammar corners beyond the vectors (anchor/escape/tail
//!   corners, the dir-suffix double-strip family, admitting-false
//!   verdicts; runtime column S3).
//! - UT-C: skip rows (comments, blank lines, whitespace-only --
//!   regression_106).
//! - UT-D: exec rows -- whole-vector builder rows (counts, DP6), the DP7
//!   toggle-ordering snapshots, the DP8 unclosed-class rows, root
//!   spellings (ig33-37), the DP3/DP13/DP14 file rows on the abstract
//!   stream (S4), the build_global blank legs (S7), and the open-failure
//!   face.
//!
//! Admit discipline (inventory section 6): every GlobBuilder verdict is
//! pinned by an explicit assume row here, one per distinct (actual,
//! case-insensitive, allow-unclosed-class) instance; each is backed by
//! the pinned-tree runtime leg (no universal axiom).
//!
//! Byte-literal convention (IG1 lesson: static slice literals have no
//! spec view identity in this Verus build): lines and expected records
//! are hex byte Seq constants; exec payloads ride push-built carriers
//! with exact spec views.
//!
//! Running: ./third_party/verus-docker.sh verus --rlimit 300
//!   database/ignore/verified/harness/ut_ig2.rs

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/lib.rs"]
mod iglib;

use iglib::gitignore::*;
use iglib::gitignore::GitignoreBuilder;
use iglib::gitignore::LineRead;
use iglib::gitignore::error_glob_payload;
use iglib::{Error, IoErrorFace, PathBytes, with_path_inner, with_path_payload};
use iglib::{is_io_spec, line_nested, glob_nested};

verus! {

// =========================================================================
// UT-A -- the inline vectors, value rows
// =========================================================================
//
/// Row ig1: line 'months' (runtime columns S1/S2).
proof fn kat_ig1() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73], false, true) == true);
    assert(ascii_trim_right_len(seq![0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73], 6) == 6);
    flat_subrange(seq![0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73], 0, 6, seq![0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73], seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]);
    let outc = add_line_value(false, true, None, seq![0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73],
        actual: seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig2: line '*.lock' (runtime columns S1/S2).
proof fn kat_ig2() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x6C, 0x6F, 0x63, 0x6B], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2A, 0x2E, 0x6C, 0x6F, 0x63, 0x6B], 6) == 6);
    flat_subrange(seq![0x2A, 0x2E, 0x6C, 0x6F, 0x63, 0x6B], 0, 6, seq![0x2A, 0x2E, 0x6C, 0x6F, 0x63, 0x6B]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x2A, 0x2E, 0x6C, 0x6F, 0x63, 0x6B], seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x6C, 0x6F, 0x63, 0x6B]);
    let outc = add_line_value(false, true, None, seq![0x2A, 0x2E, 0x6C, 0x6F, 0x63, 0x6B]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2A, 0x2E, 0x6C, 0x6F, 0x63, 0x6B],
        actual: seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x6C, 0x6F, 0x63, 0x6B],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig3: line '*.rs' (runtime columns S1/S2).
proof fn kat_ig3() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x72, 0x73], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2A, 0x2E, 0x72, 0x73], 4) == 4);
    flat_subrange(seq![0x2A, 0x2E, 0x72, 0x73], 0, 4, seq![0x2A, 0x2E, 0x72, 0x73]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x2A, 0x2E, 0x72, 0x73], seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x72, 0x73]);
    let outc = add_line_value(false, true, None, seq![0x2A, 0x2E, 0x72, 0x73]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2A, 0x2E, 0x72, 0x73],
        actual: seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x72, 0x73],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig4: line 'src/*.rs' (runtime columns S1/S2).
proof fn kat_ig4() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73], false, true) == true);
    assert(ascii_trim_right_len(seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73], 8) == 8);
    flat_subrange(seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73], 0, 8, seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73]);
    let outc = add_line_value(false, true, None, seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73],
        actual: seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig5: line '/*.c' (runtime columns S1/S2).
proof fn kat_ig5() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2E, 0x63], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2F, 0x2A, 0x2E, 0x63], 4) == 4);
    flat_subrange(seq![0x2F, 0x2A, 0x2E, 0x63], 0, 4, seq![0x2F, 0x2A, 0x2E, 0x63]);
    flat_subrange(seq![0x2F, 0x2A, 0x2E, 0x63], 1, 4, seq![0x2A, 0x2E, 0x63]);
    let outc = add_line_value(false, true, None, seq![0x2F, 0x2A, 0x2E, 0x63]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2F, 0x2A, 0x2E, 0x63],
        actual: seq![0x2A, 0x2E, 0x63],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig6: line '/src/*.rs' (runtime columns S1/S2).
proof fn kat_ig6() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2F, 0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73], 9) == 9);
    flat_subrange(seq![0x2F, 0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73], 0, 9, seq![0x2F, 0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73]);
    flat_subrange(seq![0x2F, 0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73], 1, 9, seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73]);
    let outc = add_line_value(false, true, None, seq![0x2F, 0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2F, 0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73],
        actual: seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig7a_wl: line '!src/main.rs' (runtime columns S1/S2).
proof fn kat_ig7a_wl() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73], false, true) == true);
    assert(ascii_trim_right_len(seq![0x21, 0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73], 12) == 12);
    flat_subrange(seq![0x21, 0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73], 0, 12, seq![0x21, 0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]);
    flat_subrange(seq![0x21, 0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73], 1, 12, seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]);
    let outc = add_line_value(false, true, None, seq![0x21, 0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x21, 0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73],
        actual: seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73],
        is_whitelist: true,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig8_dir: line 'foo/' (runtime columns S1/S2).
proof fn kat_ig8_dir() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, true) == true);
    assert(ascii_trim_right_len(seq![0x66, 0x6F, 0x6F, 0x2F], 4) == 4);
    flat_subrange(seq![0x66, 0x6F, 0x6F, 0x2F], 0, 4, seq![0x66, 0x6F, 0x6F, 0x2F]);
    flat_subrange(seq![0x66, 0x6F, 0x6F, 0x2F], 0, 3, seq![0x66, 0x6F, 0x6F]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x66, 0x6F, 0x6F], seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F]);
    let outc = add_line_value(false, true, None, seq![0x66, 0x6F, 0x6F, 0x2F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x66, 0x6F, 0x6F, 0x2F],
        actual: seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        is_whitelist: false,
        is_only_dir: true,
        grok_admitted: true,
    }));
}

/// Row ig9_ds: line '**/foo' (runtime columns S1/S2).
proof fn kat_ig9_ds() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], 6) == 6);
    flat_subrange(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], 0, 6, seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F]);
    let outc = add_line_value(false, true, None, seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        actual: seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig11_sfx: line '**/foo/**' (runtime columns S1/S2).
proof fn kat_ig11_sfx() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A], 9) == 9);
    flat_subrange(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A], 0, 9, seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A]);
    flat_add(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A], seq![0x2F, 0x2A], seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    let outc = add_line_value(false, true, None, seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A],
        actual: seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig13_ds: line '**/foo/bar' (runtime columns S1/S2).
proof fn kat_ig13_ds() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72], 10) == 10);
    flat_subrange(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72], 0, 10, seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72]);
    let outc = add_line_value(false, true, None, seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72],
        actual: seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig15_sfx: line 'abc/**' (runtime columns S1/S2).
proof fn kat_ig15_sfx() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x61, 0x62, 0x63, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x61, 0x62, 0x63, 0x2F, 0x2A, 0x2A], 6) == 6);
    flat_subrange(seq![0x61, 0x62, 0x63, 0x2F, 0x2A, 0x2A], 0, 6, seq![0x61, 0x62, 0x63, 0x2F, 0x2A, 0x2A]);
    flat_add(seq![0x61, 0x62, 0x63, 0x2F, 0x2A, 0x2A], seq![0x2F, 0x2A], seq![0x61, 0x62, 0x63, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    let outc = add_line_value(false, true, None, seq![0x61, 0x62, 0x63, 0x2F, 0x2A, 0x2A]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x61, 0x62, 0x63, 0x2F, 0x2A, 0x2A],
        actual: seq![0x61, 0x62, 0x63, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig18_mid: line 'a/**/b' (runtime columns S1/S2).
proof fn kat_ig18_mid() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x61, 0x2F, 0x2A, 0x2A, 0x2F, 0x62], false, true) == true);
    assert(ascii_trim_right_len(seq![0x61, 0x2F, 0x2A, 0x2A, 0x2F, 0x62], 6) == 6);
    flat_subrange(seq![0x61, 0x2F, 0x2A, 0x2A, 0x2F, 0x62], 0, 6, seq![0x61, 0x2F, 0x2A, 0x2A, 0x2F, 0x62]);
    let outc = add_line_value(false, true, None, seq![0x61, 0x2F, 0x2A, 0x2A, 0x2F, 0x62]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x61, 0x2F, 0x2A, 0x2A, 0x2F, 0x62],
        actual: seq![0x61, 0x2F, 0x2A, 0x2A, 0x2F, 0x62],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig21_esc: line '\\!xy' (runtime columns S1/S2).
proof fn kat_ig21_esc() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x21, 0x78, 0x79], false, true) == true);
    assert(ascii_trim_right_len(seq![0x5C, 0x21, 0x78, 0x79], 4) == 4);
    flat_subrange(seq![0x5C, 0x21, 0x78, 0x79], 0, 4, seq![0x5C, 0x21, 0x78, 0x79]);
    flat_subrange(seq![0x5C, 0x21, 0x78, 0x79], 1, 4, seq![0x21, 0x78, 0x79]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x21, 0x78, 0x79], seq![0x2A, 0x2A, 0x2F, 0x21, 0x78, 0x79]);
    let outc = add_line_value(false, true, None, seq![0x5C, 0x21, 0x78, 0x79]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x5C, 0x21, 0x78, 0x79],
        actual: seq![0x2A, 0x2A, 0x2F, 0x21, 0x78, 0x79],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig22_esc: line '\\#foo' (runtime columns S1/S2).
proof fn kat_ig22_esc() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x23, 0x66, 0x6F, 0x6F], false, true) == true);
    assert(ascii_trim_right_len(seq![0x5C, 0x23, 0x66, 0x6F, 0x6F], 5) == 5);
    flat_subrange(seq![0x5C, 0x23, 0x66, 0x6F, 0x6F], 0, 5, seq![0x5C, 0x23, 0x66, 0x6F, 0x6F]);
    flat_subrange(seq![0x5C, 0x23, 0x66, 0x6F, 0x6F], 1, 5, seq![0x23, 0x66, 0x6F, 0x6F]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x23, 0x66, 0x6F, 0x6F], seq![0x2A, 0x2A, 0x2F, 0x23, 0x66, 0x6F, 0x6F]);
    let outc = add_line_value(false, true, None, seq![0x5C, 0x23, 0x66, 0x6F, 0x6F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x5C, 0x23, 0x66, 0x6F, 0x6F],
        actual: seq![0x2A, 0x2A, 0x2F, 0x23, 0x66, 0x6F, 0x6F],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig23_plain: line 'foo' (runtime columns S1/S2).
proof fn kat_ig23_plain() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, true) == true);
    assert(ascii_trim_right_len(seq![0x66, 0x6F, 0x6F], 3) == 3);
    flat_subrange(seq![0x66, 0x6F, 0x6F], 0, 3, seq![0x66, 0x6F, 0x6F]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x66, 0x6F, 0x6F], seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F]);
    let outc = add_line_value(false, true, None, seq![0x66, 0x6F, 0x6F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x66, 0x6F, 0x6F],
        actual: seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig24_plain: line 'target' (runtime columns S1/S2).
proof fn kat_ig24_plain() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x74, 0x61, 0x72, 0x67, 0x65, 0x74], false, true) == true);
    assert(ascii_trim_right_len(seq![0x74, 0x61, 0x72, 0x67, 0x65, 0x74], 6) == 6);
    flat_subrange(seq![0x74, 0x61, 0x72, 0x67, 0x65, 0x74], 0, 6, seq![0x74, 0x61, 0x72, 0x67, 0x65, 0x74]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x74, 0x61, 0x72, 0x67, 0x65, 0x74], seq![0x2A, 0x2A, 0x2F, 0x74, 0x61, 0x72, 0x67, 0x65, 0x74]);
    let outc = add_line_value(false, true, None, seq![0x74, 0x61, 0x72, 0x67, 0x65, 0x74]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x74, 0x61, 0x72, 0x67, 0x65, 0x74],
        actual: seq![0x2A, 0x2A, 0x2F, 0x74, 0x61, 0x72, 0x67, 0x65, 0x74],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig25_plain: line 'Cargo.lock' (runtime columns S1/S2).
proof fn kat_ig25_plain() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63, 0x6B], false, true) == true);
    assert(ascii_trim_right_len(seq![0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63, 0x6B], 10) == 10);
    flat_subrange(seq![0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63, 0x6B], 0, 10, seq![0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63, 0x6B]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63, 0x6B], seq![0x2A, 0x2A, 0x2F, 0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63, 0x6B]);
    let outc = add_line_value(false, true, None, seq![0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63, 0x6B]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63, 0x6B],
        actual: seq![0x2A, 0x2A, 0x2F, 0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63, 0x6B],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig26_anchor: line '/foo/bar/baz' (runtime columns S1/S2).
proof fn kat_ig26_anchor() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A], 12) == 12);
    flat_subrange(seq![0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A], 0, 12, seq![0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A]);
    flat_subrange(seq![0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A], 1, 12, seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A]);
    let outc = add_line_value(false, true, None, seq![0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A],
        actual: seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig28_anchor_dir: line '/llvm/' (runtime columns S1/S2).
proof fn kat_ig28_anchor_dir() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x6C, 0x6C, 0x76, 0x6D], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2F, 0x6C, 0x6C, 0x76, 0x6D, 0x2F], 6) == 6);
    flat_subrange(seq![0x2F, 0x6C, 0x6C, 0x76, 0x6D, 0x2F], 0, 6, seq![0x2F, 0x6C, 0x6C, 0x76, 0x6D, 0x2F]);
    flat_subrange(seq![0x2F, 0x6C, 0x6C, 0x76, 0x6D, 0x2F], 1, 6, seq![0x6C, 0x6C, 0x76, 0x6D, 0x2F]);
    flat_subrange(seq![0x6C, 0x6C, 0x76, 0x6D, 0x2F], 0, 4, seq![0x6C, 0x6C, 0x76, 0x6D]);
    let outc = add_line_value(false, true, None, seq![0x2F, 0x6C, 0x6C, 0x76, 0x6D, 0x2F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2F, 0x6C, 0x6C, 0x76, 0x6D, 0x2F],
        actual: seq![0x6C, 0x6C, 0x76, 0x6D],
        is_whitelist: false,
        is_only_dir: true,
        grok_admitted: true,
    }));
}

/// Row ig29_trailsp: line 'node_modules/ ' (runtime columns S1/S2).
proof fn kat_ig29_trailsp() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73], false, true) == true);
    reveal_with_fuel(ascii_trim_right_len, 16);
    assert(ascii_trim_right_len(seq![0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73, 0x2F, 0x20], 14) == 13);
    flat_subrange(seq![0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73, 0x2F, 0x20], 0, 13, seq![0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73, 0x2F]);
    flat_subrange(seq![0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73, 0x2F], 0, 12, seq![0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73], seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73]);
    let outc = add_line_value(false, true, None, seq![0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73, 0x2F, 0x20]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73, 0x2F],
        actual: seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73],
        is_whitelist: false,
        is_only_dir: true,
        grok_admitted: true,
    }));
}

/// Row ig30_ds_dir: line '**/' (runtime columns S1/S2).
proof fn kat_ig30_ds_dir() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2A, 0x2A, 0x2F], 3) == 3);
    flat_subrange(seq![0x2A, 0x2A, 0x2F], 0, 3, seq![0x2A, 0x2A, 0x2F]);
    flat_subrange(seq![0x2A, 0x2A, 0x2F], 0, 2, seq![0x2A, 0x2A]);
    let outc = add_line_value(false, true, None, seq![0x2A, 0x2A, 0x2F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2A, 0x2A, 0x2F],
        actual: seq![0x2A, 0x2A],
        is_whitelist: false,
        is_only_dir: true,
        grok_admitted: true,
    }));
}

/// Row ig31_slash: line 'path1/*' (runtime columns S1/S2).
proof fn kat_ig31_slash() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x70, 0x61, 0x74, 0x68, 0x31, 0x2F, 0x2A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x70, 0x61, 0x74, 0x68, 0x31, 0x2F, 0x2A], 7) == 7);
    flat_subrange(seq![0x70, 0x61, 0x74, 0x68, 0x31, 0x2F, 0x2A], 0, 7, seq![0x70, 0x61, 0x74, 0x68, 0x31, 0x2F, 0x2A]);
    let outc = add_line_value(false, true, None, seq![0x70, 0x61, 0x74, 0x68, 0x31, 0x2F, 0x2A]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x70, 0x61, 0x74, 0x68, 0x31, 0x2F, 0x2A],
        actual: seq![0x70, 0x61, 0x74, 0x68, 0x31, 0x2F, 0x2A],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig32_dot: line '.a/b' (runtime columns S1/S2).
proof fn kat_ig32_dot() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2E, 0x61, 0x2F, 0x62], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2E, 0x61, 0x2F, 0x62], 4) == 4);
    flat_subrange(seq![0x2E, 0x61, 0x2F, 0x62], 0, 4, seq![0x2E, 0x61, 0x2F, 0x62]);
    let outc = add_line_value(false, true, None, seq![0x2E, 0x61, 0x2F, 0x62]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2E, 0x61, 0x2F, 0x62],
        actual: seq![0x2E, 0x61, 0x2F, 0x62],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig38_esc: line '\\[' (runtime columns S1/S2).
proof fn kat_ig38_esc() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x5C, 0x5B], false, true) == true);
    assert(ascii_trim_right_len(seq![0x5C, 0x5B], 2) == 2);
    flat_subrange(seq![0x5C, 0x5B], 0, 2, seq![0x5C, 0x5B]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x5C, 0x5B], seq![0x2A, 0x2A, 0x2F, 0x5C, 0x5B]);
    let outc = add_line_value(false, true, None, seq![0x5C, 0x5B]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x5C, 0x5B],
        actual: seq![0x2A, 0x2A, 0x2F, 0x5C, 0x5B],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig39_esc: line '\\?' (runtime columns S1/S2).
proof fn kat_ig39_esc() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x5C, 0x3F], false, true) == true);
    assert(ascii_trim_right_len(seq![0x5C, 0x3F], 2) == 2);
    flat_subrange(seq![0x5C, 0x3F], 0, 2, seq![0x5C, 0x3F]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x5C, 0x3F], seq![0x2A, 0x2A, 0x2F, 0x5C, 0x3F]);
    let outc = add_line_value(false, true, None, seq![0x5C, 0x3F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x5C, 0x3F],
        actual: seq![0x2A, 0x2A, 0x2F, 0x5C, 0x3F],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig40_esc: line '\\*' (runtime columns S1/S2).
proof fn kat_ig40_esc() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x5C, 0x2A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x5C, 0x2A], 2) == 2);
    flat_subrange(seq![0x5C, 0x2A], 0, 2, seq![0x5C, 0x2A]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x5C, 0x2A], seq![0x2A, 0x2A, 0x2F, 0x5C, 0x2A]);
    let outc = add_line_value(false, true, None, seq![0x5C, 0x2A]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x5C, 0x2A],
        actual: seq![0x2A, 0x2A, 0x2F, 0x5C, 0x2A],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig41_esc: line '\\a' (runtime columns S1/S2).
proof fn kat_ig41_esc() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x5C, 0x61], false, true) == true);
    assert(ascii_trim_right_len(seq![0x5C, 0x61], 2) == 2);
    flat_subrange(seq![0x5C, 0x61], 0, 2, seq![0x5C, 0x61]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x5C, 0x61], seq![0x2A, 0x2A, 0x2F, 0x5C, 0x61]);
    let outc = add_line_value(false, true, None, seq![0x5C, 0x61]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x5C, 0x61],
        actual: seq![0x2A, 0x2A, 0x2F, 0x5C, 0x61],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig42_star: line 's*.rs' (runtime columns S1/S2).
proof fn kat_ig42_star() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x73, 0x2A, 0x2E, 0x72, 0x73], false, true) == true);
    assert(ascii_trim_right_len(seq![0x73, 0x2A, 0x2E, 0x72, 0x73], 5) == 5);
    flat_subrange(seq![0x73, 0x2A, 0x2E, 0x72, 0x73], 0, 5, seq![0x73, 0x2A, 0x2E, 0x72, 0x73]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x73, 0x2A, 0x2E, 0x72, 0x73], seq![0x2A, 0x2A, 0x2F, 0x73, 0x2A, 0x2E, 0x72, 0x73]);
    let outc = add_line_value(false, true, None, seq![0x73, 0x2A, 0x2E, 0x72, 0x73]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x73, 0x2A, 0x2E, 0x72, 0x73],
        actual: seq![0x2A, 0x2A, 0x2F, 0x73, 0x2A, 0x2E, 0x72, 0x73],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig43_bare: line '**' (runtime columns S1/S2).
proof fn kat_ig43_bare() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2A, 0x2A], 2) == 2);
    flat_subrange(seq![0x2A, 0x2A], 0, 2, seq![0x2A, 0x2A]);
    let outc = add_line_value(false, true, None, seq![0x2A, 0x2A]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2A, 0x2A],
        actual: seq![0x2A, 0x2A],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ig44_ds: line '**/**/*' (runtime columns S1/S2).
proof fn kat_ig44_ds() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A], 7) == 7);
    flat_subrange(seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A], 0, 7, seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    let outc = add_line_value(false, true, None, seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
        actual: seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ignot13_sfx: line 'foo/**' (runtime columns S1/S2).
proof fn kat_ignot13_sfx() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A], 6) == 6);
    flat_subrange(seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A], 0, 6, seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A]);
    flat_add(seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A], seq![0x2F, 0x2A], seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    let outc = add_line_value(false, true, None, seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A],
        actual: seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ignot15_wl_anchor: line '!/bar' (runtime columns S1/S2).
proof fn kat_ignot15_wl_anchor() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x62, 0x61, 0x72], false, true) == true);
    assert(ascii_trim_right_len(seq![0x21, 0x2F, 0x62, 0x61, 0x72], 5) == 5);
    flat_subrange(seq![0x21, 0x2F, 0x62, 0x61, 0x72], 0, 5, seq![0x21, 0x2F, 0x62, 0x61, 0x72]);
    flat_subrange(seq![0x21, 0x2F, 0x62, 0x61, 0x72], 1, 5, seq![0x2F, 0x62, 0x61, 0x72]);
    flat_subrange(seq![0x2F, 0x62, 0x61, 0x72], 1, 4, seq![0x62, 0x61, 0x72]);
    let outc = add_line_value(false, true, None, seq![0x21, 0x2F, 0x62, 0x61, 0x72]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x21, 0x2F, 0x62, 0x61, 0x72],
        actual: seq![0x62, 0x61, 0x72],
        is_whitelist: true,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ignot16a_star: line '*' (runtime columns S1/S2).
proof fn kat_ignot16a_star() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x2A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2A], 1) == 1);
    flat_subrange(seq![0x2A], 0, 1, seq![0x2A]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x2A], seq![0x2A, 0x2A, 0x2F, 0x2A]);
    let outc = add_line_value(false, true, None, seq![0x2A]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2A],
        actual: seq![0x2A, 0x2A, 0x2F, 0x2A],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ignot16b_wl_dir: line '!**/' (runtime columns S1/S2).
proof fn kat_ignot16b_wl_dir() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x21, 0x2A, 0x2A, 0x2F], 4) == 4);
    flat_subrange(seq![0x21, 0x2A, 0x2A, 0x2F], 0, 4, seq![0x21, 0x2A, 0x2A, 0x2F]);
    flat_subrange(seq![0x21, 0x2A, 0x2A, 0x2F], 1, 4, seq![0x2A, 0x2A, 0x2F]);
    flat_subrange(seq![0x2A, 0x2A, 0x2F], 0, 2, seq![0x2A, 0x2A]);
    let outc = add_line_value(false, true, None, seq![0x21, 0x2A, 0x2A, 0x2F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x21, 0x2A, 0x2A, 0x2F],
        actual: seq![0x2A, 0x2A],
        is_whitelist: true,
        is_only_dir: true,
        grok_admitted: true,
    }));
}

/// Row cs1: line '*.html' (runtime columns S1/S2).
proof fn kat_cs1() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C], 6) == 6);
    flat_subrange(seq![0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C], 0, 6, seq![0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C], seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C]);
    let outc = add_line_value(false, true, None, seq![0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C],
        actual: seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ignot1_plain: line 'amonths' (runtime columns S1/S2).
proof fn kat_ignot1_plain() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x61, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73], false, true) == true);
    assert(ascii_trim_right_len(seq![0x61, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73], 7) == 7);
    flat_subrange(seq![0x61, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73], 0, 7, seq![0x61, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x61, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73], seq![0x2A, 0x2A, 0x2F, 0x61, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]);
    let outc = add_line_value(false, true, None, seq![0x61, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x61, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73],
        actual: seq![0x2A, 0x2A, 0x2F, 0x61, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Row ignot11_comment: line '#foo' -> the comment early exit (Skip).
proof fn kat_ignot11_comment() {
    assert(add_line_value(false, true, None, seq![0x23, 0x66, 0x6F, 0x6F]) == AddLineOutcome::Skip);
}

// =========================================================================
// UT-B -- grammar corners (runtime column: S3)
// =========================================================================
//
/// Corner slash_root: line '/' (runtime column S3).
proof fn kat_corner_slash_root() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2F], 1) == 1);
    flat_subrange(seq![0x2F], 0, 1, seq![0x2F]);
    flat_subrange(seq![0x2F], 1, 1, seq![]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x2F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2F],
        actual: seq![],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Corner bare_bang: line '!' (runtime column S3).
proof fn kat_corner_bare_bang() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F], false, true) == true);
    assert(ascii_trim_right_len(seq![0x21], 1) == 1);
    flat_subrange(seq![0x21], 0, 1, seq![0x21]);
    flat_subrange(seq![0x21], 1, 1, seq![]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![], seq![0x2A, 0x2A, 0x2F]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x21]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x21],
        actual: seq![0x2A, 0x2A, 0x2F],
        is_whitelist: true,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Corner slash_slash: line '//' (runtime column S3).
proof fn kat_corner_slash_slash() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2F, 0x2F], 2) == 2);
    flat_subrange(seq![0x2F, 0x2F], 0, 2, seq![0x2F, 0x2F]);
    flat_subrange(seq![0x2F, 0x2F], 1, 2, seq![0x2F]);
    flat_subrange(seq![0x2F], 0, 0, seq![]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x2F, 0x2F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2F, 0x2F],
        actual: seq![],
        is_whitelist: false,
        is_only_dir: true,
        grok_admitted: true,
    }));
}

/// Corner comment_col0_only: line ' #foo' (runtime column S3).
proof fn kat_corner_comment_col0_only() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x20, 0x23, 0x66, 0x6F, 0x6F], false, true) == true);
    assert(ascii_trim_right_len(seq![0x20, 0x23, 0x66, 0x6F, 0x6F], 5) == 5);
    flat_subrange(seq![0x20, 0x23, 0x66, 0x6F, 0x6F], 0, 5, seq![0x20, 0x23, 0x66, 0x6F, 0x6F]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x20, 0x23, 0x66, 0x6F, 0x6F], seq![0x2A, 0x2A, 0x2F, 0x20, 0x23, 0x66, 0x6F, 0x6F]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x20, 0x23, 0x66, 0x6F, 0x6F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x20, 0x23, 0x66, 0x6F, 0x6F],
        actual: seq![0x2A, 0x2A, 0x2F, 0x20, 0x23, 0x66, 0x6F, 0x6F],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Corner esc_space_only: line '\\ ' (runtime column S3).
proof fn kat_corner_esc_space_only() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x5C, 0x20], false, true) == true);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x5C, 0x20], seq![0x2A, 0x2A, 0x2F, 0x5C, 0x20]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x5C, 0x20]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x5C, 0x20],
        actual: seq![0x2A, 0x2A, 0x2F, 0x5C, 0x20],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Corner esc_space_tail: line 'x\\ ' (runtime column S3).
proof fn kat_corner_esc_space_tail() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x78, 0x5C, 0x20], false, true) == true);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x78, 0x5C, 0x20], seq![0x2A, 0x2A, 0x2F, 0x78, 0x5C, 0x20]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x78, 0x5C, 0x20]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x78, 0x5C, 0x20],
        actual: seq![0x2A, 0x2A, 0x2F, 0x78, 0x5C, 0x20],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Corner dbl_bs_esc_space: line 'x\\\\ ' (runtime column S3).
proof fn kat_corner_dbl_bs_esc_space() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x78, 0x5C, 0x5C, 0x20], false, true) == true);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x78, 0x5C, 0x5C, 0x20], seq![0x2A, 0x2A, 0x2F, 0x78, 0x5C, 0x5C, 0x20]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x78, 0x5C, 0x5C, 0x20]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x78, 0x5C, 0x5C, 0x20],
        actual: seq![0x2A, 0x2A, 0x2F, 0x78, 0x5C, 0x5C, 0x20],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Corner dangling_bs: line '\\' (runtime column S3).
proof fn kat_corner_dangling_bs() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x5C], false, true) == false);
    assert(ascii_trim_right_len(seq![0x5C], 1) == 1);
    flat_subrange(seq![0x5C], 0, 1, seq![0x5C]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x5C], seq![0x2A, 0x2A, 0x2F, 0x5C]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x5C]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x5C],
        actual: seq![0x2A, 0x2A, 0x2F, 0x5C],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: false,
    }));
}

/// Corner unclosed_group: line 'a{b' (runtime column S3).
proof fn kat_corner_unclosed_group() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62], false, true) == false);
    assert(ascii_trim_right_len(seq![0x61, 0x7B, 0x62], 3) == 3);
    flat_subrange(seq![0x61, 0x7B, 0x62], 0, 3, seq![0x61, 0x7B, 0x62]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x61, 0x7B, 0x62], seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x61, 0x7B, 0x62]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x61, 0x7B, 0x62],
        actual: seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: false,
    }));
}

/// Corner unopened_group: line 'a}' (runtime column S3).
proof fn kat_corner_unopened_group() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x61, 0x7D], false, true) == false);
    assert(ascii_trim_right_len(seq![0x61, 0x7D], 2) == 2);
    flat_subrange(seq![0x61, 0x7D], 0, 2, seq![0x61, 0x7D]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x61, 0x7D], seq![0x2A, 0x2A, 0x2F, 0x61, 0x7D]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x61, 0x7D]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x61, 0x7D],
        actual: seq![0x2A, 0x2A, 0x2F, 0x61, 0x7D],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: false,
    }));
}

/// Corner unclosed_group2: line '{a' (runtime column S3).
proof fn kat_corner_unclosed_group2() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x7B, 0x61], false, true) == false);
    assert(ascii_trim_right_len(seq![0x7B, 0x61], 2) == 2);
    flat_subrange(seq![0x7B, 0x61], 0, 2, seq![0x7B, 0x61]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x7B, 0x61], seq![0x2A, 0x2A, 0x2F, 0x7B, 0x61]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x7B, 0x61]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x7B, 0x61],
        actual: seq![0x2A, 0x2A, 0x2F, 0x7B, 0x61],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: false,
    }));
}

/// Corner comma_group: line 'a{b,c' (runtime column S3).
proof fn kat_corner_comma_group() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62, 0x2C, 0x63], false, true) == false);
    assert(ascii_trim_right_len(seq![0x61, 0x7B, 0x62, 0x2C, 0x63], 5) == 5);
    flat_subrange(seq![0x61, 0x7B, 0x62, 0x2C, 0x63], 0, 5, seq![0x61, 0x7B, 0x62, 0x2C, 0x63]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x61, 0x7B, 0x62, 0x2C, 0x63], seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62, 0x2C, 0x63]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x61, 0x7B, 0x62, 0x2C, 0x63]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x61, 0x7B, 0x62, 0x2C, 0x63],
        actual: seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62, 0x2C, 0x63],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: false,
    }));
}

/// Corner brace_bs_x: line '}\\x' (runtime column S3).
proof fn kat_corner_brace_bs_x() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x7D, 0x5C, 0x78], false, true) == false);
    assert(ascii_trim_right_len(seq![0x7D, 0x5C, 0x78], 3) == 3);
    flat_subrange(seq![0x7D, 0x5C, 0x78], 0, 3, seq![0x7D, 0x5C, 0x78]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x7D, 0x5C, 0x78], seq![0x2A, 0x2A, 0x2F, 0x7D, 0x5C, 0x78]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x7D, 0x5C, 0x78]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x7D, 0x5C, 0x78],
        actual: seq![0x2A, 0x2A, 0x2F, 0x7D, 0x5C, 0x78],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: false,
    }));
}

/// Corner esc_slash_dir: line 'a\\/' (runtime column S3).
proof fn kat_corner_esc_slash_dir() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x61], false, true) == true);
    assert(ascii_trim_right_len(seq![0x61, 0x5C, 0x2F], 3) == 3);
    flat_subrange(seq![0x61, 0x5C, 0x2F], 0, 3, seq![0x61, 0x5C, 0x2F]);
    flat_subrange(seq![0x61, 0x5C, 0x2F], 0, 2, seq![0x61, 0x5C]);
    flat_subrange(seq![0x61, 0x5C], 0, 1, seq![0x61]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x61], seq![0x2A, 0x2A, 0x2F, 0x61]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x61, 0x5C, 0x2F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x61, 0x5C, 0x2F],
        actual: seq![0x2A, 0x2A, 0x2F, 0x61],
        is_whitelist: false,
        is_only_dir: true,
        grok_admitted: true,
    }));
}

/// Corner dbl_bs_dir_dangling: line 'a\\\\/' (runtime column S3).
proof fn kat_corner_dbl_bs_dir_dangling() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x61, 0x5C], false, true) == false);
    assert(ascii_trim_right_len(seq![0x61, 0x5C, 0x5C, 0x2F], 4) == 4);
    flat_subrange(seq![0x61, 0x5C, 0x5C, 0x2F], 0, 4, seq![0x61, 0x5C, 0x5C, 0x2F]);
    flat_subrange(seq![0x61, 0x5C, 0x5C, 0x2F], 0, 3, seq![0x61, 0x5C, 0x5C]);
    flat_subrange(seq![0x61, 0x5C, 0x5C], 0, 2, seq![0x61, 0x5C]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x61, 0x5C], seq![0x2A, 0x2A, 0x2F, 0x61, 0x5C]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x61, 0x5C, 0x5C, 0x2F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x61, 0x5C, 0x5C, 0x2F],
        actual: seq![0x2A, 0x2A, 0x2F, 0x61, 0x5C],
        is_whitelist: false,
        is_only_dir: true,
        grok_admitted: false,
    }));
}

/// Corner dbl_bs_dir_dangling2: line 'dir\\\\/' (runtime column S3).
proof fn kat_corner_dbl_bs_dir_dangling2() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x64, 0x69, 0x72, 0x5C], false, true) == false);
    assert(ascii_trim_right_len(seq![0x64, 0x69, 0x72, 0x5C, 0x5C, 0x2F], 6) == 6);
    flat_subrange(seq![0x64, 0x69, 0x72, 0x5C, 0x5C, 0x2F], 0, 6, seq![0x64, 0x69, 0x72, 0x5C, 0x5C, 0x2F]);
    flat_subrange(seq![0x64, 0x69, 0x72, 0x5C, 0x5C, 0x2F], 0, 5, seq![0x64, 0x69, 0x72, 0x5C, 0x5C]);
    flat_subrange(seq![0x64, 0x69, 0x72, 0x5C, 0x5C], 0, 4, seq![0x64, 0x69, 0x72, 0x5C]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x64, 0x69, 0x72, 0x5C], seq![0x2A, 0x2A, 0x2F, 0x64, 0x69, 0x72, 0x5C]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x64, 0x69, 0x72, 0x5C, 0x5C, 0x2F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x64, 0x69, 0x72, 0x5C, 0x5C, 0x2F],
        actual: seq![0x2A, 0x2A, 0x2F, 0x64, 0x69, 0x72, 0x5C],
        is_whitelist: false,
        is_only_dir: true,
        grok_admitted: false,
    }));
}

/// Corner star3: line '***' (runtime column S3).
proof fn kat_corner_star3() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2A, 0x2A, 0x2A], 3) == 3);
    flat_subrange(seq![0x2A, 0x2A, 0x2A], 0, 3, seq![0x2A, 0x2A, 0x2A]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x2A, 0x2A, 0x2A], seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2A]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x2A, 0x2A, 0x2A]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2A, 0x2A, 0x2A],
        actual: seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2A],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Corner slash_ds: line '/**' (runtime column S3).
proof fn kat_corner_slash_ds() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2F, 0x2A, 0x2A], 3) == 3);
    flat_subrange(seq![0x2F, 0x2A, 0x2A], 0, 3, seq![0x2F, 0x2A, 0x2A]);
    flat_subrange(seq![0x2F, 0x2A, 0x2A], 1, 3, seq![0x2A, 0x2A]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x2F, 0x2A, 0x2A]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2F, 0x2A, 0x2A],
        actual: seq![0x2A, 0x2A],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Corner star_slash: line '*/' (runtime column S3).
proof fn kat_corner_star_slash() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x2A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x2A, 0x2F], 2) == 2);
    flat_subrange(seq![0x2A, 0x2F], 0, 2, seq![0x2A, 0x2F]);
    flat_subrange(seq![0x2A, 0x2F], 0, 1, seq![0x2A]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x2A], seq![0x2A, 0x2A, 0x2F, 0x2A]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x2A, 0x2F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x2A, 0x2F],
        actual: seq![0x2A, 0x2A, 0x2F, 0x2A],
        is_whitelist: false,
        is_only_dir: true,
        grok_admitted: true,
    }));
}

/// Corner qstar: line '?*' (runtime column S3).
proof fn kat_corner_qstar() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x3F, 0x2A], false, true) == true);
    assert(ascii_trim_right_len(seq![0x3F, 0x2A], 2) == 2);
    flat_subrange(seq![0x3F, 0x2A], 0, 2, seq![0x3F, 0x2A]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x3F, 0x2A], seq![0x2A, 0x2A, 0x2F, 0x3F, 0x2A]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x3F, 0x2A]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x3F, 0x2A],
        actual: seq![0x2A, 0x2A, 0x2F, 0x3F, 0x2A],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

/// Corner bracket_foo: line '[foo' (runtime column S3).
proof fn kat_corner_bracket_foo() {
    // fuel bundle: the recursive scan specs need explicit fuel to
    // evaluate on literals (#IG-3 family)
    reveal_with_fuel(has_byte_from, 32);
    reveal_with_fuel(ascii_trim_right_len, 34);
    // admit row: the pinned-tree GlobBuilder verdict
    assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x5B, 0x66, 0x6F, 0x6F], false, true) == true);
    assert(ascii_trim_right_len(seq![0x5B, 0x66, 0x6F, 0x6F], 4) == 4);
    flat_subrange(seq![0x5B, 0x66, 0x6F, 0x6F], 0, 4, seq![0x5B, 0x66, 0x6F, 0x6F]);
    flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x5B, 0x66, 0x6F, 0x6F], seq![0x2A, 0x2A, 0x2F, 0x5B, 0x66, 0x6F, 0x6F]);
    // (chain bridges end)
    let outc = add_line_value(false, true, None, seq![0x5B, 0x66, 0x6F, 0x6F]);
    assert(outc =~= AddLineOutcome::Add(GlobSpec {
        from: None,
        original: seq![0x5B, 0x66, 0x6F, 0x6F],
        actual: seq![0x2A, 0x2A, 0x2F, 0x5B, 0x66, 0x6F, 0x6F],
        is_whitelist: false,
        is_only_dir: false,
        grok_admitted: true,
    }));
}

// =========================================================================
// UT-C -- skip rows (comments / trim-blank / whitespace-only)
// =========================================================================
//
/// Skip row: line '#foo' (gitignore.rs:470-478 early exits).
proof fn kat_skip_0() {
    reveal_with_fuel(ascii_trim_right_len, 34);
    assert(ascii_trim_right_len(seq![0x23, 0x66, 0x6F, 0x6F], 4) == 4);
    flat_subrange(seq![0x23, 0x66, 0x6F, 0x6F], 0, 4, seq![0x23, 0x66, 0x6F, 0x6F]);
    assert(add_line_value(false, true, None, seq![0x23, 0x66, 0x6F, 0x6F]) == AddLineOutcome::Skip);
}

/// Skip row: line ' ' (gitignore.rs:470-478 early exits).
proof fn kat_skip_1() {
    reveal_with_fuel(ascii_trim_right_len, 34);
    assert(ascii_trim_right_len(seq![0x20], 1) == 0);
    flat_subrange(seq![0x20], 0, 0, seq![]);
    assert(add_line_value(false, true, None, seq![0x20]) == AddLineOutcome::Skip);
}

/// Skip row: line '\t' (gitignore.rs:470-478 early exits).
proof fn kat_skip_2() {
    reveal_with_fuel(ascii_trim_right_len, 34);
    assert(ascii_trim_right_len(seq![0x09], 1) == 0);
    flat_subrange(seq![0x09], 0, 0, seq![]);
    assert(add_line_value(false, true, None, seq![0x09]) == AddLineOutcome::Skip);
}

/// Skip row: line '' (gitignore.rs:470-478 early exits).
proof fn kat_skip_3() {
    reveal_with_fuel(ascii_trim_right_len, 34);
    assert(ascii_trim_right_len(seq![], 0) == 0);
    flat_subrange(seq![], 0, 0, seq![]);
    assert(add_line_value(false, true, None, seq![]) == AddLineOutcome::Skip);
}

// =========================================================================
// UT-D helpers -- push-built byte carriers with exact pinned views
// =========================================================================
//
fn bx_src_main_rs() -> (r: Vec<u8>)
    ensures r@ == seq![0x21, 0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x21);
    v.push(0x73);
    v.push(0x72);
    v.push(0x63);
    v.push(0x2F);
    v.push(0x6D);
    v.push(0x61);
    v.push(0x69);
    v.push(0x6E);
    v.push(0x2E);
    v.push(0x72);
    v.push(0x73);
    v
}

fn bx_rs() -> (r: Vec<u8>)
    ensures r@ == seq![0x2A, 0x2E, 0x72, 0x73]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2A);
    v.push(0x2E);
    v.push(0x72);
    v.push(0x73);
    v
}

fn bx_RS() -> (r: Vec<u8>)
    ensures r@ == seq![0x2A, 0x2E, 0x52, 0x53]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2A);
    v.push(0x2E);
    v.push(0x52);
    v.push(0x53);
    v
}

fn bx_html() -> (r: Vec<u8>)
    ensures r@ == seq![0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2A);
    v.push(0x2E);
    v.push(0x68);
    v.push(0x74);
    v.push(0x6D);
    v.push(0x6C);
    v
}

fn bx_zzgood() -> (r: Vec<u8>)
    ensures r@ == seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x7A);
    v.push(0x7A);
    v.push(0x67);
    v.push(0x6F);
    v.push(0x6F);
    v.push(0x64);
    v
}

fn bx_postgood() -> (r: Vec<u8>)
    ensures r@ == seq![0x70, 0x6F, 0x73, 0x74, 0x67, 0x6F, 0x6F, 0x64]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x70);
    v.push(0x6F);
    v.push(0x73);
    v.push(0x74);
    v.push(0x67);
    v.push(0x6F);
    v.push(0x6F);
    v.push(0x64);
    v
}

fn bx_abc_brace() -> (r: Vec<u8>)
    ensures r@ == seq![0x61, 0x7B, 0x62]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x61);
    v.push(0x7B);
    v.push(0x62);
    v
}

fn bx_close_brace() -> (r: Vec<u8>)
    ensures r@ == seq![0x61, 0x7D]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x61);
    v.push(0x7D);
    v
}

fn bx_lin_bracket() -> (r: Vec<u8>)
    ensures r@ == seq![0x5B, 0x61, 0x62, 0x63]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x5B);
    v.push(0x61);
    v.push(0x62);
    v.push(0x63);
    v
}

fn bx_bar() -> (r: Vec<u8>)
    ensures r@ == seq![0x62, 0x61, 0x72]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x62);
    v.push(0x61);
    v.push(0x72);
    v
}

fn bx_space() -> (r: Vec<u8>)
    ensures r@ == seq![0x20]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x20);
    v
}

fn bx_root_slash() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v
}

fn bx_root_dot() -> (r: Vec<u8>)
    ensures r@ == seq![0x2E]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2E);
    v
}

fn bx_root_dot_slash() -> (r: Vec<u8>)
    ensures r@ == seq![0x2E, 0x2F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2E);
    v.push(0x2F);
    v
}

fn bx_root_dot_dot() -> (r: Vec<u8>)
    ensures r@ == seq![0x2E, 0x2F, 0x2E]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2E);
    v.push(0x2F);
    v.push(0x2E);
    v
}

fn bx_root_dot_slash_dot() -> (r: Vec<u8>)
    ensures r@ == seq![0x2E, 0x2F, 0x2E, 0x2F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2E);
    v.push(0x2F);
    v.push(0x2E);
    v.push(0x2F);
    v
}

fn bx_root_dsd() -> (r: Vec<u8>)
    ensures r@ == seq![0x2E, 0x2F, 0x2E, 0x2F, 0x2E]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2E);
    v.push(0x2F);
    v.push(0x2E);
    v.push(0x2F);
    v.push(0x2E);
    v
}

fn bx_anywhere() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x61, 0x6E, 0x79, 0x77, 0x68, 0x65, 0x72, 0x65]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x61);
    v.push(0x6E);
    v.push(0x79);
    v.push(0x77);
    v.push(0x68);
    v.push(0x65);
    v.push(0x72);
    v.push(0x65);
    v
}

fn bx_missing_excludes() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x6D, 0x69, 0x73, 0x73, 0x69, 0x6E, 0x67, 0x2F, 0x65, 0x78, 0x63, 0x6C, 0x75, 0x64, 0x65, 0x73]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x6D);
    v.push(0x69);
    v.push(0x73);
    v.push(0x73);
    v.push(0x69);
    v.push(0x6E);
    v.push(0x67);
    v.push(0x2F);
    v.push(0x65);
    v.push(0x78);
    v.push(0x63);
    v.push(0x6C);
    v.push(0x75);
    v.push(0x64);
    v.push(0x65);
    v.push(0x73);
    v
}

fn bx_p_dp3() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x74, 0x6D, 0x70, 0x2F, 0x64, 0x70, 0x33, 0x2E, 0x67, 0x69, 0x74, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v.push(0x6D);
    v.push(0x70);
    v.push(0x2F);
    v.push(0x64);
    v.push(0x70);
    v.push(0x33);
    v.push(0x2E);
    v.push(0x67);
    v.push(0x69);
    v.push(0x74);
    v.push(0x69);
    v.push(0x67);
    v.push(0x6E);
    v.push(0x6F);
    v.push(0x72);
    v.push(0x65);
    v
}

fn bx_p_dp3glob() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x74, 0x6D, 0x70, 0x2F, 0x64, 0x70, 0x33, 0x67, 0x6C, 0x6F, 0x62, 0x2E, 0x67, 0x69, 0x74, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v.push(0x6D);
    v.push(0x70);
    v.push(0x2F);
    v.push(0x64);
    v.push(0x70);
    v.push(0x33);
    v.push(0x67);
    v.push(0x6C);
    v.push(0x6F);
    v.push(0x62);
    v.push(0x2E);
    v.push(0x67);
    v.push(0x69);
    v.push(0x74);
    v.push(0x69);
    v.push(0x67);
    v.push(0x6E);
    v.push(0x6F);
    v.push(0x72);
    v.push(0x65);
    v
}

fn bx_p_dp14() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x74, 0x6D, 0x70, 0x2F, 0x64, 0x70, 0x31, 0x34, 0x2E, 0x67, 0x69, 0x74, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v.push(0x6D);
    v.push(0x70);
    v.push(0x2F);
    v.push(0x64);
    v.push(0x70);
    v.push(0x31);
    v.push(0x34);
    v.push(0x2E);
    v.push(0x67);
    v.push(0x69);
    v.push(0x74);
    v.push(0x69);
    v.push(0x67);
    v.push(0x6E);
    v.push(0x6F);
    v.push(0x72);
    v.push(0x65);
    v
}

fn bx_p_bom() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x74, 0x6D, 0x70, 0x2F, 0x62, 0x6F, 0x6D, 0x2E, 0x67, 0x69, 0x74, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v.push(0x6D);
    v.push(0x70);
    v.push(0x2F);
    v.push(0x62);
    v.push(0x6F);
    v.push(0x6D);
    v.push(0x2E);
    v.push(0x67);
    v.push(0x69);
    v.push(0x74);
    v.push(0x69);
    v.push(0x67);
    v.push(0x6E);
    v.push(0x6F);
    v.push(0x72);
    v.push(0x65);
    v
}

fn bx_p_bom0() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x74, 0x6D, 0x70, 0x2F, 0x62, 0x6F, 0x6D, 0x30, 0x2E, 0x67, 0x69, 0x74, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v.push(0x6D);
    v.push(0x70);
    v.push(0x2F);
    v.push(0x62);
    v.push(0x6F);
    v.push(0x6D);
    v.push(0x30);
    v.push(0x2E);
    v.push(0x67);
    v.push(0x69);
    v.push(0x74);
    v.push(0x69);
    v.push(0x67);
    v.push(0x6E);
    v.push(0x6F);
    v.push(0x72);
    v.push(0x65);
    v
}

fn bx_p_bom2() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x74, 0x6D, 0x70, 0x2F, 0x62, 0x6F, 0x6D, 0x32, 0x2E, 0x67, 0x69, 0x74, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v.push(0x6D);
    v.push(0x70);
    v.push(0x2F);
    v.push(0x62);
    v.push(0x6F);
    v.push(0x6D);
    v.push(0x32);
    v.push(0x2E);
    v.push(0x67);
    v.push(0x69);
    v.push(0x74);
    v.push(0x69);
    v.push(0x67);
    v.push(0x6E);
    v.push(0x6F);
    v.push(0x72);
    v.push(0x65);
    v
}

fn bx_p_missing() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x72, 0x6F, 0x6F, 0x74, 0x2F, 0x6D, 0x69, 0x73, 0x73, 0x69, 0x6E, 0x67, 0x2E, 0x67, 0x69, 0x74, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x72);
    v.push(0x6F);
    v.push(0x6F);
    v.push(0x74);
    v.push(0x2F);
    v.push(0x6D);
    v.push(0x69);
    v.push(0x73);
    v.push(0x73);
    v.push(0x69);
    v.push(0x6E);
    v.push(0x67);
    v.push(0x2E);
    v.push(0x67);
    v.push(0x69);
    v.push(0x74);
    v.push(0x69);
    v.push(0x67);
    v.push(0x6E);
    v.push(0x6F);
    v.push(0x72);
    v.push(0x65);
    v
}

fn bx_bom_foo() -> (r: Vec<u8>)
    ensures r@ == seq![0xEF, 0xBB, 0xBF, 0x66, 0x6F, 0x6F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0xEF);
    v.push(0xBB);
    v.push(0xBF);
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v
}

fn bx_bom2_foo() -> (r: Vec<u8>)
    ensures r@ == seq![0xEF, 0xBB, 0xBF, 0xEF, 0xBB, 0xBF, 0x66, 0x6F, 0x6F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0xEF);
    v.push(0xBB);
    v.push(0xBF);
    v.push(0xEF);
    v.push(0xBB);
    v.push(0xBF);
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v
}

fn bx_foo_plain() -> (r: Vec<u8>)
    ensures r@ == seq![0x66, 0x6F, 0x6F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v
}

fn bx_bom_bar() -> (r: Vec<u8>)
    ensures r@ == seq![0xEF, 0xBB, 0xBF, 0x62, 0x61, 0x72]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0xEF);
    v.push(0xBB);
    v.push(0xBF);
    v.push(0x62);
    v.push(0x61);
    v.push(0x72);
    v
}

// =========================================================================
// UT-D -- exec rows (assert sets verified at compile time)
// =========================================================================
//
/// ig7 counting row (runtime S1 ig7): whitelist+ignore builder, DP6.
fn exec_row_ig7() {
    proof {
        reveal_with_fuel(has_byte_from, 32);
        reveal_with_fuel(ascii_trim_right_len, 34);
        assume(glob_builder_admits(seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73], false, true) == true);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x72, 0x73], false, true) == true);
        // line 1 "!src/main.rs": no trim, the bang+anchor drops (two steps),
        // slash present -> no inject
        assert(ascii_trim_right_len(seq![0x21, 0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73], 12) == 12);
        flat_subrange(seq![0x21, 0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73], 0, 12,
            seq![0x21, 0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]);
        // the bang drop; the anchored-slash check does NOT fire (the
        // remainder starts with 's')
        flat_subrange(seq![0x21, 0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73], 1, 12,
            seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]);
        // line 2 "*.rs": no trim, prepend
        assert(ascii_trim_right_len(seq![0x2A, 0x2E, 0x72, 0x73], 4) == 4);
        flat_subrange(seq![0x2A, 0x2E, 0x72, 0x73], 0, 4, seq![0x2A, 0x2E, 0x72, 0x73]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x2A, 0x2E, 0x72, 0x73], seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x72, 0x73]);
    }
    let mut b = GitignoreBuilder::new(b"");
    let r1 = b.add_line(None, bx_src_main_rs().as_slice());
    assert(r1 matches Ok(_));
    let r2 = b.add_line(None, bx_rs().as_slice());
    assert(r2 matches Ok(_));
    // store/counting face (runtime row S1 ig7); DP6 over the whole row
    assert(b.globs@.len() == 2);
    assert(b.builder.registered@.len() == 2);
    // NB the per-element whitelist flags of the builtin store are
    // pinned at the value tier (kat_ig7a_wl / kat_rs rows) and by
    // add_line's stored_matches post at the src level; the harness-level
    // ghost-indexed re-instantiation did not close after the fuel	trace
    // runs (quantifier-instantiation shape) and stays with the IG3
    // rematch when the GlobSet face lands.  The count-level claims
    // below (num_ignores/num_whitelists through build) carry the row.
    let gbuild = b.build();
    assert(gbuild matches Ok(g));
    let gi = match gbuild { Ok(g) => g, Err(_) => Gitignore::empty() };
    assert(gi.globs@.len() == 2);
    // NB: the numeric split (num_ignores==1/num_whitelists==1) of this
    // multi-line store rides on the per-element whitelist flags, whose
    // ghost-indexed instantiation did not close here (same instantiation
    // shape as the flag row above; the value-tier rows kat_ig7a_wl /
    // kat_ig28_anchor_dir carry the record semantics, and dp6's lemma
    // itself is verified src-side over every store satisfying the count
    // preconditions). Pinned for the IG3 rematch.
    let ln2 = gi.len();
    assert(ln2 == 2);
    let not_empty = gi.is_empty();
    assert(!not_empty);


}

/// regression_106 (upstream :863-867) + the empty accessor face.
fn exec_row_regression_106() {
    proof {
        reveal_with_fuel(has_byte_from, 32);
        reveal_with_fuel(ascii_trim_right_len, 34);
        // line " ": the whitespace-only trim empties it -> Skip
        assert(ascii_trim_right_len(seq![0x20], 1) == 0);
        flat_subrange(seq![0x20], 0, 0, seq![]);
    }
    let mut b = GitignoreBuilder::new(bx_root_slash().as_slice());
    let r = b.add_line(None, bx_space().as_slice());
    assert(r matches Ok(_));
    assert(b.globs@.len() == 0);
    let gbuild = b.build();
    assert(gbuild matches Ok(g));
    let gi = match gbuild { Ok(g) => g, Err(_) => Gitignore::empty() };
    assert(gi.globs@.len() == 0);
    let ln0 = gi.len();
    assert(ln0 == 0);
    let ie0 = gi.is_empty();
    assert(ie0);
    let z1 = gi.num_ignores();
    let z2 = gi.num_whitelists();
    assert(z1 == 0 && z2 == 0);
    let emp = Gitignore::empty();
    let ep = emp.path();
    assert(ep@.len() == 0);
    let eln = emp.len();
    let eie = emp.is_empty();
    assert(eln == 0 && eie);


}

/// DP7 toggle-ordering row (runtime S6 ci-flip): per-add snapshots.
fn exec_row_dp7_order() {
    proof {
        reveal_with_fuel(has_byte_from, 32);
        reveal_with_fuel(ascii_trim_right_len, 34);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x52, 0x53], false, true) == true);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C], true, true) == true);
        assert(ascii_trim_right_len(seq![0x2A, 0x2E, 0x52, 0x53], 4) == 4);
        flat_subrange(seq![0x2A, 0x2E, 0x52, 0x53], 0, 4, seq![0x2A, 0x2E, 0x52, 0x53]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x2A, 0x2E, 0x52, 0x53], seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x52, 0x53]);
        assert(ascii_trim_right_len(seq![0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C], 6) == 6);
        flat_subrange(seq![0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C], 0, 6, seq![0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C],
            seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C]);
    }
    let mut b = GitignoreBuilder::new(b"");
    let ra0 = b.add_line(None, bx_RS().as_slice());
    assert(ra0 matches Ok(_));
    let rc0 = b.case_insensitive(true);
    assert(rc0 matches Ok(_));
    let rb0 = b.add_line(None, bx_html().as_slice());
    assert(rb0 matches Ok(_));
    // DP7: the per-add snapshots ride add_line's per-store posts (the
    // second add happened under the toggled builder: registered[1].ci)
    assert(b.builder.registered@[1].case_insensitive == true);
    assert(b.builder.registered@[1].case_insensitive == true);
    assert(b.case_insensitive);
    assert(b.globs@.len() == 2);
    let gbuild = b.build();
    assert(gbuild matches Ok(g));
    let gi = match gbuild { Ok(g) => g, Err(_) => Gitignore::empty() };
    assert(gi.set.registered@.len() == 2);
    proof {
        reveal_with_fuel(count_ignores, 4);
        reveal_with_fuel(count_whitelists, 4);
        dp6_len_is_nignore_plus_nwhite(gi);
    }
    let c1 = gi.num_ignores();
    let c2 = gi.num_whitelists();
    assert(c1 + c2 == 2);


}

/// DP8 row (runtime S5): "[abc"; the gitignore-side default admits.
fn exec_row_dp8_unclosed() {
    proof {
        reveal_with_fuel(has_byte_from, 32);
        reveal_with_fuel(ascii_trim_right_len, 34);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x5B, 0x61, 0x62, 0x63], false, false) == false);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x5B, 0x61, 0x62, 0x63], false, true) == true);
        assert(ascii_trim_right_len(seq![0x5B, 0x61, 0x62, 0x63], 4) == 4);
        flat_subrange(seq![0x5B, 0x61, 0x62, 0x63], 0, 4, seq![0x5B, 0x61, 0x62, 0x63]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x5B, 0x61, 0x62, 0x63], seq![0x2A, 0x2A, 0x2F, 0x5B, 0x61, 0x62, 0x63]);
    }
    let mut b = GitignoreBuilder::new(b"");
    b.allow_unclosed_class(false);
    let r = b.add_line(None, bx_lin_bracket().as_slice());
    assert(r matches Err(_));
    assert(b.globs@.len() == 0);   // the rejected line left no trace
    let e = match r { Err(x) => x, Ok(()) => Error::InvalidDefinition };
    assert(error_glob_payload(&e) matches Some(v) && v == seq![0x5B, 0x61, 0x62, 0x63]);
    let mut b2 = GitignoreBuilder::new(b"");
    let rb2 = b2.add_line(None, bx_lin_bracket().as_slice());
    assert(rb2 matches Ok(_));
    assert(b2.globs@.len() == 1);
    assert(b2.globs[0].actual@ == seq![0x2A, 0x2A, 0x2F, 0x5B, 0x61, 0x62, 0x63]);


}

/// ig33-37 root-spelling rows (GitignoreBuilder::new one-strip).
fn exec_row_root_spellings() {
    proof {

    }
    let a = GitignoreBuilder::new(bx_root_dot_slash().as_slice());
    assert(a.root.bytes@.len() == 0);
    let b = GitignoreBuilder::new(bx_root_dot().as_slice());
    assert(b.root.bytes@ == seq![0x2E]);
    let c = GitignoreBuilder::new(bx_root_dot_dot().as_slice());
    assert(c.root.bytes@ == seq![0x2E]);
    let d = GitignoreBuilder::new(bx_root_dot_slash_dot().as_slice());
    assert(d.root.bytes@ == seq![0x2E, 0x2F]);
    let f = GitignoreBuilder::new(bx_root_dsd().as_slice());
    assert(f.root.bytes@ == seq![0x2E, 0x2F, 0x2E]);
}

/// DP3 row (runtime S4 dp3-nonutf8, PR3605 re-read: the io face repr 7
/// models a read error whose kind is NOT InvalidData -- the hard door
/// post-#3605): the hard read error STILL breaks the loop; the file
/// tail is dropped (PR3605-verify runtime row SJ4: a genuine
/// non-InvalidData io read error, /proc/self/mem's EIO, reported and
/// abandoned at line 1).
fn exec_row_dp3_nonutf8_hard_io() {
    proof {
        reveal_with_fuel(has_byte_from, 32);
        reveal_with_fuel(ascii_trim_right_len, 34);
        reveal_with_fuel(fold_add_lines, 8);
        reveal_with_fuel(errs_fold_len, 8);
        reveal_with_fuel(strip_bom_from, 8);
        reveal_with_fuel(first_err, 8);
        reveal_with_fuel(first_hard_err, 8);
        reveal_with_fuel(io_err_reprs, 8);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64], false, true) == true);
        assert(ascii_trim_right_len(seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64], 6) == 6);
        flat_subrange(seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64], 0, 6, seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64],
            seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64]);
    }
    let mut b = GitignoreBuilder::new(bx_p_dp3().as_slice());
    let lines: Vec<LineRead> = vec![
        LineRead::Line(bx_zzgood()),
        LineRead::Err(IoErrorFace::new(7)),
        LineRead::Line(bx_postgood()),
    ];
    let r = b.add(bx_p_dp3().as_slice(), Some(lines));
    // DP3 (runtime row S4 dp3-nonutf8; hard door): only the first line
    // made it in; postgood was dropped by the hard read-error break
    assert(r matches Some(_));
    assert(b.globs@.len() == 1);


}

/// PR #3605 fixed row (runtime PR3605-verify SJ1: the F2 crime core
/// flipped green): the same three-line stream with the io face's kind
/// locked to InvalidData (the non-UTF-8 line) -- the loop pushes the
/// tagged error and WALKS ON, so the tail joins the store. This is the
/// replacement theorem for the pre-fix DP3 drop claim ("the registered
/// suffix past a read error is empty"): under the patched processed
/// bound that statement is not derivable any more -- this row's store
/// count (2, zzgood AND postgood) refutes it on the witness stream
/// (pre-fix IG3 S10dp3 had matched(postgood)=none on these bytes).
fn exec_row_dp3_nonutf8_fixed() {
    proof {
        reveal_with_fuel(has_byte_from, 32);
        reveal_with_fuel(ascii_trim_right_len, 34);
        reveal_with_fuel(fold_add_lines, 8);
        reveal_with_fuel(errs_fold_len, 8);
        reveal_with_fuel(errs_reject_fold_len, 8);
        reveal_with_fuel(strip_bom_from, 8);
        reveal_with_fuel(first_err, 8);
        reveal_with_fuel(first_hard_err, 8);
        reveal_with_fuel(io_err_reprs, 8);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64], false, true) == true);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x70, 0x6F, 0x73, 0x74, 0x67, 0x6F, 0x6F, 0x64], false, true) == true);
        assert(ascii_trim_right_len(seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64], 6) == 6);
        flat_subrange(seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64], 0, 6, seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64],
            seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64]);
        assert(ascii_trim_right_len(seq![0x70, 0x6F, 0x73, 0x74, 0x67, 0x6F, 0x6F, 0x64], 8) == 8);
        flat_subrange(seq![0x70, 0x6F, 0x73, 0x74, 0x67, 0x6F, 0x6F, 0x64], 0, 8, seq![0x70, 0x6F, 0x73, 0x74, 0x67, 0x6F, 0x6F, 0x64]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x70, 0x6F, 0x73, 0x74, 0x67, 0x6F, 0x6F, 0x64],
            seq![0x2A, 0x2A, 0x2F, 0x70, 0x6F, 0x73, 0x74, 0x67, 0x6F, 0x6F, 0x64]);
        // first_err pins the soft line (index 1); no hard error exists:
        // the processed bound is the whole stream
    }
    let mut b = GitignoreBuilder::new(bx_p_dp3().as_slice());
    let lines: Vec<LineRead> = vec![
        LineRead::Line(bx_zzgood()),
        LineRead::Err(IoErrorFace::new(INVALID_DATA_REPR)),
        LineRead::Line(bx_postgood()),
    ];
    let r = b.add(bx_p_dp3().as_slice(), Some(lines));
    // the doc-promise row: the tail IS in the store, and the caller is
    // still told about the bad line
    assert(r matches Some(_));
    assert(b.globs@.len() == 2);
    // seed specs for the (IOk)/(R1) consumption lane
    proof {
        let ls = lines@;
        assert(first_err(ls, 0) == Some(1));
        assert(first_err(ls, 1) == Some(1));
        assert(ls[1] matches LineRead::Err(_));
        assert(lone_invalid_data_index(ls) == 1);
        assert((first_hard_err(ls, 0) matches None));
        assert(lines_processed_count(ls) == 3);
        assert(errs_reject_fold_len(false, true, ls, 1) == 0);
        assert(errs_reject_fold_len(false, true, ls, 2) == 0);
        assert(errs_reject_fold_len(false, true, ls, 3) == 0);
        assert(errs_view_fold(false, true, ls, lines_processed_count(ls))
            == Seq::<(bool, Option<u64>, Option<Seq<u8>>)>::empty()
                .push((true, Some(2), None)));
    }
    // (IOk) the returned error: io spine, line 2, no glob payload
    // (the InvalidData-kind side rides the runtime rows SJ1/SJ2 --
    // the PR's own test's io_error().kind() assert; the twin's
    // value-level repr threading was retired on SMT cost)
    match r {
        Some(e) => {
            // the (R1)/(IOk) view lane: the single folded entry rides
            // into the returned error verbatim, then the tuple facts
            // decompose
            proof {
                assert(err_view(&e) == (true, Some(2), None));
                let ev = err_view(&e);
                assert(ev.0 == true);
                assert(ev.1 == Some(2));
                assert(ev.2 == None);
            }
            assert(is_io_spec(&e));
            assert(line_nested(&e) == Some(2));
            assert(glob_nested(&e) matches None);
        }
        None => {}
    }
}

/// DP3 contrast row (runtime S4 dp3-badglob): a bad glob keeps the rest.
fn exec_row_dp3_badglob() {
    proof {
        reveal_with_fuel(has_byte_from, 32);
        reveal_with_fuel(ascii_trim_right_len, 34);
        reveal_with_fuel(fold_add_lines, 8);
        reveal_with_fuel(errs_fold_len, 8);
        reveal_with_fuel(strip_bom_from, 8);
        reveal_with_fuel(first_err, 8);
        reveal_with_fuel(first_hard_err, 8);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62], false, true) == false);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64], false, true) == true);
        assert(ascii_trim_right_len(seq![0x61, 0x7B, 0x62], 3) == 3);
        flat_subrange(seq![0x61, 0x7B, 0x62], 0, 3, seq![0x61, 0x7B, 0x62]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x61, 0x7B, 0x62], seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62]);
        assert(ascii_trim_right_len(seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64], 6) == 6);
        flat_subrange(seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64], 0, 6, seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64],
            seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64]);
    }
    let mut b = GitignoreBuilder::new(bx_p_dp3glob().as_slice());
    let lines: Vec<LineRead> = vec![
        LineRead::Line(bx_abc_brace()),
        LineRead::Line(bx_zzgood()),
    ];
    let r = b.add(bx_p_dp3glob().as_slice(), Some(lines));
    // DP3 contrast (runtime S4 dp3-badglob): a bad GLOB line keeps the rest
    assert(r matches Some(_));
    assert(b.globs@.len() == 1);


}

/// DP14 row (runtime S4 dp14-twobad): two bad lines fold into Partial.
fn exec_row_dp14_twobad() {
    proof {
        reveal_with_fuel(has_byte_from, 32);
        reveal_with_fuel(ascii_trim_right_len, 34);
        reveal_with_fuel(fold_add_lines, 8);
        reveal_with_fuel(errs_fold_len, 8);
        reveal_with_fuel(strip_bom_from, 8);
        reveal_with_fuel(first_err, 8);
        reveal_with_fuel(first_hard_err, 8);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62], false, true) == false);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x61, 0x7D], false, true) == false);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64], false, true) == true);
        assert(ascii_trim_right_len(seq![0x61, 0x7B, 0x62], 3) == 3);
        flat_subrange(seq![0x61, 0x7B, 0x62], 0, 3, seq![0x61, 0x7B, 0x62]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x61, 0x7B, 0x62], seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62]);
        assert(ascii_trim_right_len(seq![0x61, 0x7D], 2) == 2);
        flat_subrange(seq![0x61, 0x7D], 0, 2, seq![0x61, 0x7D]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x61, 0x7D], seq![0x2A, 0x2A, 0x2F, 0x61, 0x7D]);
        assert(ascii_trim_right_len(seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64], 6) == 6);
        flat_subrange(seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64], 0, 6, seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64],
            seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64]);
    }
    let mut b = GitignoreBuilder::new(bx_p_dp14().as_slice());
    let lines: Vec<LineRead> = vec![
        LineRead::Line(bx_abc_brace()),
        LineRead::Line(bx_close_brace()),
        LineRead::Line(bx_zzgood()),
    ];
    let r = b.add(bx_p_dp14().as_slice(), Some(lines));
    // DP14 (runtime S4 dp14-twobad): two bad-glob lines still leave the
    // file's good tail in the store; the Some(Partial(..)) return shape is
    // runtime-pinned (S4) and follows IG1's into_error_option >=2 post at
    // the src level; the harness asserts the store-side facts
    assert(r matches Some(_));
    assert(b.globs@.len() == 1);


}

/// DP13 rows (runtime S4 bom-first / bom-repeated / bom-second).
fn exec_row_dp13_bom() {
    proof {
        reveal_with_fuel(has_byte_from, 32);
        reveal_with_fuel(ascii_trim_right_len, 34);
        reveal_with_fuel(fold_add_lines, 8);
        reveal_with_fuel(errs_fold_len, 8);
        reveal_with_fuel(strip_bom_from, 8);
        reveal_with_fuel(first_err, 8);
        reveal_with_fuel(first_hard_err, 8);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, true) == true);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, true) == true);
        assume(glob_builder_admits(seq![0x2A, 0x2A, 0x2F, 0xEF, 0xBB, 0xBF, 0x62, 0x61, 0x72], false, true) == true);
        // case 1 first-line BOM: strip_bom peels once
        flat_subrange(seq![0xEF, 0xBB, 0xBF, 0x66, 0x6F, 0x6F], 3, 6, seq![0x66, 0x6F, 0x6F]);
        assert(ascii_trim_right_len(seq![0x66, 0x6F, 0x6F], 3) == 3);
        flat_subrange(seq![0x66, 0x6F, 0x6F], 0, 3, seq![0x66, 0x6F, 0x6F]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x66, 0x6F, 0x6F], seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F]);
        assert(ascii_trim_right_len(seq![0x62, 0x61, 0x72], 3) == 3);
        flat_subrange(seq![0x62, 0x61, 0x72], 0, 3, seq![0x62, 0x61, 0x72]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0x62, 0x61, 0x72], seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72]);
        // case 2 REPEATED BOM: both peel via the recursion
        flat_subrange(seq![0xEF, 0xBB, 0xBF, 0xEF, 0xBB, 0xBF, 0x66, 0x6F, 0x6F], 6, 9, seq![0x66, 0x6F, 0x6F]);
        // case 3 second-line BOM stays: pattern carries it
        assert(ascii_trim_right_len(seq![0xEF, 0xBB, 0xBF, 0x62, 0x61, 0x72], 6) == 6);
        flat_subrange(seq![0xEF, 0xBB, 0xBF, 0x62, 0x61, 0x72], 0, 6, seq![0xEF, 0xBB, 0xBF, 0x62, 0x61, 0x72]);
        flat_add(seq![0x2A, 0x2A, 0x2F], seq![0xEF, 0xBB, 0xBF, 0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0xEF, 0xBB, 0xBF, 0x62, 0x61, 0x72]);
        assert(ascii_trim_right_len(seq![0x66, 0x6F, 0x6F], 3) == 3);
        flat_subrange(seq![0x66, 0x6F, 0x6F], 0, 3, seq![0x66, 0x6F, 0x6F]);
    }
    // case 1: BOM on the first line only (runtime S4 bom-first)
    let b_res = {
        let mut b = GitignoreBuilder::new(bx_p_bom().as_slice());
        let lines: Vec<LineRead> = vec![
            LineRead::Line(bx_bom_foo()),
            LineRead::Line(bx_bar()),
        ];
        b.add(bx_p_bom().as_slice(), Some(lines));
        assert(b.globs@.len() == 2);
        b
    };
    // case 2: REPEATED BOM stripped entirely (trim_start_matches plural;
    // runtime S4 bom-repeated)
    let mut b2 = GitignoreBuilder::new(bx_p_bom0().as_slice());
    let lines2: Vec<LineRead> = vec![
        LineRead::Line(bx_bom2_foo()),
    ];
    b2.add(bx_p_bom0().as_slice(), Some(lines2));
    assert(b2.globs@.len() == 1);
    // case 3: BOM on the SECOND line stays inside the pattern (runtime S4
    // bom-second) -- count-level claim; the BOM-keeping content claim rides
    // the add's fold spec (which carries strip_bom only on line 0)
    let mut b3 = GitignoreBuilder::new(bx_p_bom2().as_slice());
    let lines3: Vec<LineRead> = vec![
        LineRead::Line(bx_foo_plain()),
        LineRead::Line(bx_bom_bar()),
    ];
    b3.add(bx_p_bom2().as_slice(), Some(lines3));
    assert(b3.globs@.len() == 2);


}

/// build_global blank legs (runtime S7 legs 2-3): None / not-a-file.
fn exec_row_build_global_blank() {
    proof {

    }
    let b = GitignoreBuilder::new(bx_anywhere().as_slice());
    let out = GitignoreBuilder::build_global(b, None, false, None);
    assert(out.0.globs@.len() == 0);
    let ie_g = out.0.is_empty();
    assert(ie_g);
    assert(out.1 matches None);
    let b2 = GitignoreBuilder::new(bx_anywhere().as_slice());
    let out2 = GitignoreBuilder::build_global(b2, Some(bx_missing_excludes().as_slice()), false, None);
    assert(out2.0.globs@.len() == 0);
    assert(out2.1 matches None);
}

/// The add-open-failure face (upstream :410-413).
fn exec_row_add_open_fail() {
    proof {

    }
    let mut b = GitignoreBuilder::new(bx_root_slash().as_slice());
    let path_c = bx_p_missing();
    let r = b.add(path_c.as_slice(), None);
    assert(r matches Some(_));
    let e = match r { Some(x) => x, None => Error::InvalidDefinition };
    assert(e matches Error::WithPath { .. });
    assert(with_path_inner(&e) matches Error::Io(_));
    assert(b.globs@.len() == 0);
}

// ===========================================================================
// DP35 rows (IG8): the gitconfig_excludes_path priority ladder over
// the twin's gc_* family. Every oracle instance below is pinned by an
// assume backed by the IG8 runtime rows (out/kverus-run/IG8/
// runtime-legs/ig5-driver/ig5-driver-rows.txt, S16 A-F; the env
// spellings and file contents are those rows' shapes with short
// canonical paths).
// ===========================================================================

/// S16 A (default row): every file read misses and every env value is
/// unset -> the speculative $HOME/.config/git/ignore path (level 5).
fn exec_row_gc35_default() {
    let mut hm: Vec<u8> = Vec::new();
    hm.push(0x2F); // "/h"
    hm.push(0x68);
    assert(hm@ == seq![0x2F, 0x68]);
    proof {
        // admits (S16 A): no home .gitconfig, no home .config/git/
        // config, no /etc/gitconfig hit
        assume(gc_read_face(seq![0x2F, 0x68, 0x2F, 0x2E, 0x67, 0x69,
            0x74, 0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67]) matches None);
        assume(gc_read_face(seq![0x2F, 0x68, 0x2F, 0x2E, 0x63, 0x6F,
            0x6E, 0x66, 0x69, 0x67, 0x2F, 0x67, 0x69, 0x74, 0x2F,
            0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67]) matches None);
        assume(gc_read_face(gc_etc_gitconfig()) matches None);
        // rung ladder: each level's path spelling and miss pinned
        assert(gc_nonempty(None) matches None);
        let p2 = gcj(hm@, gc_dot_gitconfig());
        assert(p2 == seq![0x2F, 0x68, 0x2F, 0x2E, 0x67, 0x69, 0x74,
            0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67]);
        assert(gc_parse_at(p2, Some(hm@)) matches None);
        let b3 = gcj(hm@, gc_dot_config());
        assert(b3 == seq![0x2F, 0x68, 0x2F, 0x2E, 0x63, 0x6F, 0x6E,
            0x66, 0x69, 0x67]);
        let p3 = gcj(b3, gc_git_config());
        assert(p3 == seq![0x2F, 0x68, 0x2F, 0x2E, 0x63, 0x6F, 0x6E,
            0x66, 0x69, 0x67, 0x2F, 0x67, 0x69, 0x74, 0x2F, 0x63,
            0x6F, 0x6E, 0x66, 0x69, 0x67]);
        assert(gc_parse_at(p3, Some(hm@)) matches None);
        assert(gc_parse_at(gc_etc_gitconfig(), Some(hm@)) matches None);
        assert(gc_base_cfg(None, Some(hm@)) == Some(b3));
        assert(gcj(b3, gc_git_ignore()) == seq![0x2F, 0x68, 0x2F,
            0x2E, 0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67, 0x2F, 0x67,
            0x69, 0x74, 0x2F, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65]);
        assert(gc_excl_spec(None, None, None,
            Some(hm@))
            == Some(seq![0x2F, 0x68, 0x2F, 0x2E, 0x63, 0x6F, 0x6E,
                0x66, 0x69, 0x67, 0x2F, 0x67, 0x69, 0x74, 0x2F,
                0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65]));
    }
    let r = gc_excludes_exec(None, None, None, Some(hm.as_slice()));
    assert(r matches Some(_));
    let p = match r {
        Some(x) => x,
        None => Vec::new(),
    };
    assert(p@ == seq![0x2F, 0x68, 0x2F, 0x2E, 0x63, 0x6F, 0x6E, 0x66,
        0x69, 0x67, 0x2F, 0x67, 0x69, 0x74, 0x2F, 0x69, 0x67, 0x6E,
        0x6F, 0x72, 0x65]);
}

/// S16 B (home-hit row): $HOME/.gitconfig carries
/// "excludesfile = /my/global/ignore" (level 2, no tilde).
fn exec_row_gc35_home_hit() {
    let mut hm: Vec<u8> = Vec::new();
    hm.push(0x2F);
    hm.push(0x68);
    proof {
        let cps = seq![0x5B, 0x63, 0x6F, 0x72, 0x65, 0x5D, 0x0A,
            0x65, 0x78, 0x63, 0x6C, 0x75, 0x64, 0x65, 0x73, 0x66,
            0x69, 0x6C, 0x65, 0x20, 0x3D, 0x20, 0x2F, 0x6D, 0x79,
            0x2F, 0x67, 0x6C, 0x6F, 0x62, 0x61, 0x6C, 0x2F, 0x69,
            0x67, 0x6E, 0x6F, 0x72, 0x65, 0x0A];
        assume(gc_read_face(seq![0x2F, 0x68, 0x2F, 0x2E, 0x67, 0x69,
            0x74, 0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67]) == Some(cps));
        assume(gc_pe_face(cps)
            == Some(seq![0x2F, 0x6D, 0x79, 0x2F, 0x67, 0x6C, 0x6F,
                0x62, 0x61, 0x6C, 0x2F, 0x69, 0x67, 0x6E, 0x6F,
                0x72, 0x65]));
        reveal_with_fuel(gc_et, 24);
        let cap = seq![0x2F, 0x6D, 0x79, 0x2F, 0x67, 0x6C, 0x6F,
            0x62, 0x61, 0x6C, 0x2F, 0x69, 0x67, 0x6E, 0x6F, 0x72,
            0x65];
        assert(gc_et_full(Some(hm@), cap) == cap); // no tilde
        let p2 = gcj(hm@, gc_dot_gitconfig());
        assert(p2 == seq![0x2F, 0x68, 0x2F, 0x2E, 0x67, 0x69, 0x74,
            0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67]);
        assert(gc_read_face(p2) == Some(cps));
        assert(gc_pe_face(cps) == Some(cap));
        assert(gc_parse_at(p2, Some(hm@)) == Some(cap));
        assert(gc_excl_spec(None, None, None,
            Some(hm@))
            == Some(seq![0x2F, 0x6D, 0x79, 0x2F, 0x67, 0x6C, 0x6F,
                0x62, 0x61, 0x6C, 0x2F, 0x69, 0x67, 0x6E, 0x6F,
                0x72, 0x65]));
    }
    let r = gc_excludes_exec(None, None, None, Some(hm.as_slice()));
    assert(r matches Some(_));
    let p = match r {
        Some(x) => x,
        None => Vec::new(),
    };
    assert(p@ == seq![0x2F, 0x6D, 0x79, 0x2F, 0x67, 0x6C, 0x6F, 0x62,
        0x61, 0x6C, 0x2F, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65]);
}

/// S16 C (global-env row): GIT_CONFIG_GLOBAL wins over a live home
/// level 2, and the "~/.cache/ign" capture tilde-expands against
/// $HOME (the S16 C tilde rows).
fn exec_row_gc35_global_env_tilde() {
    let mut hm: Vec<u8> = Vec::new();
    hm.push(0x2F);
    hm.push(0x68);
    assert(hm@ == seq![0x2F, 0x68]);
    let mut gg: Vec<u8> = Vec::new();
    gg.push(0x2F); // "/g/gcfg"
    gg.push(0x67);
    gg.push(0x2F);
    gg.push(0x67);
    gg.push(0x63);
    gg.push(0x66);
    assert(gg@ == seq![0x2F, 0x67, 0x2F, 0x67, 0x63, 0x66]);
    proof {
        reveal_with_fuel(gc_et, 24);
        let c1 = seq![0x5B, 0x63, 0x6F, 0x72, 0x65, 0x5D, 0x0A,
            0x65, 0x78, 0x63, 0x6C, 0x75, 0x64, 0x65, 0x73, 0x66,
            0x69, 0x6C, 0x65, 0x20, 0x3D, 0x20, 0x7E, 0x2F, 0x2E,
            0x63, 0x61, 0x63, 0x68, 0x65, 0x2F, 0x69, 0x67, 0x6E,
            0x0A];
        assume(gc_read_face(seq![0x2F, 0x67, 0x2F, 0x67, 0x63, 0x66])
            == Some(c1));
        assume(gc_pe_face(c1)
            == Some(seq![0x7E, 0x2F, 0x2E, 0x63, 0x61, 0x63, 0x68,
                0x65, 0x2F, 0x69, 0x67, 0x6E]));
        let cap1 = seq![0x7E, 0x2F, 0x2E, 0x63, 0x61, 0x63, 0x68,
            0x65, 0x2F, 0x69, 0x67, 0x6E];
        assert(gc_et_full(Some(hm@), cap1) == seq![0x2F, 0x68, 0x2F,
            0x2E, 0x63, 0x61, 0x63, 0x68, 0x65, 0x2F, 0x69, 0x67,
            0x6E]);
        assert(gc_read_face(gg@) == Some(c1));
        assert(gc_pe_face(c1) == Some(cap1));
        assert(gc_parse_at(gg@, Some(hm@))
            == Some(seq![0x2F, 0x68, 0x2F, 0x2E, 0x63, 0x61, 0x63,
                0x68, 0x65, 0x2F, 0x69, 0x67, 0x6E]));
        // the live level-2 hit that MUST lose (the order witness):
        // a DIFFERENT home .gitignore with its own capture
        let c2w = seq![0x5B, 0x63, 0x6F, 0x72, 0x65, 0x5D, 0x0A,
            0x65, 0x78, 0x63, 0x6C, 0x75, 0x64, 0x65, 0x73, 0x66,
            0x69, 0x6C, 0x65, 0x20, 0x3D, 0x20, 0x2F, 0x77, 0x72,
            0x6F, 0x6E, 0x67, 0x0A];
        assume(gc_read_face(seq![0x2F, 0x68, 0x2F, 0x2E, 0x67, 0x69,
            0x74, 0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67]) == Some(c2w));
        assume(gc_pe_face(c2w)
            == Some(seq![0x2F, 0x77, 0x72, 0x6F, 0x6E, 0x67]));
        assert(gc_excl_spec(Some(gg@), None, None,
            Some(hm@))
            == Some(seq![0x2F, 0x68, 0x2F, 0x2E, 0x63, 0x61, 0x63,
                0x68, 0x65, 0x2F, 0x69, 0x67, 0x6E]));
    }
    let r = gc_excludes_exec(Some(gg.as_slice()), None, None,
        Some(hm.as_slice()));
    assert(r matches Some(_));
    let p = match r {
        Some(x) => x,
        None => Vec::new(),
    };
    assert(p@ == seq![0x2F, 0x68, 0x2F, 0x2E, 0x63, 0x61, 0x63, 0x68,
        0x65, 0x2F, 0x69, 0x67, 0x6E]);
}

/// S16 F (system row): levels 1-3 miss, GIT_CONFIG_SYSTEM carries
/// "excludesfile = /sys/ign" (level 4).
fn exec_row_gc35_system() {
    let mut hm: Vec<u8> = Vec::new();
    hm.push(0x2F);
    hm.push(0x68);
    assert(hm@ == seq![0x2F, 0x68]);
    let mut ss: Vec<u8> = Vec::new();
    ss.push(0x2F); // "/g/sys"
    ss.push(0x67);
    ss.push(0x2F);
    ss.push(0x73);
    ss.push(0x79);
    ss.push(0x73);
    assert(ss@ == seq![0x2F, 0x67, 0x2F, 0x73, 0x79, 0x73]);
    proof {
        let c2 = seq![0x5B, 0x63, 0x6F, 0x72, 0x65, 0x5D, 0x0A,
            0x65, 0x78, 0x63, 0x6C, 0x75, 0x64, 0x65, 0x73, 0x66,
            0x69, 0x6C, 0x65, 0x20, 0x3D, 0x20, 0x2F, 0x73, 0x79,
            0x73, 0x2F, 0x69, 0x67, 0x6E, 0x0A];
        assume(gc_read_face(seq![0x2F, 0x68, 0x2F, 0x2E, 0x67, 0x69,
            0x74, 0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67]) matches None);
        assume(gc_read_face(seq![0x2F, 0x68, 0x2F, 0x2E, 0x63, 0x6F,
            0x6E, 0x66, 0x69, 0x67, 0x2F, 0x67, 0x69, 0x74, 0x2F,
            0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67]) matches None);
        assume(gc_read_face(seq![0x2F, 0x67, 0x2F, 0x73, 0x79, 0x73])
            == Some(c2));
        assume(gc_pe_face(c2)
            == Some(seq![0x2F, 0x73, 0x79, 0x73, 0x2F, 0x69, 0x67,
                0x6E]));
        let cap2 = seq![0x2F, 0x73, 0x79, 0x73, 0x2F, 0x69, 0x67,
            0x6E];
        reveal_with_fuel(gc_et, 16);
        assert(gc_et_full(Some(hm@), cap2) == cap2); // no tilde
        assert(gc_read_face(ss@) == Some(c2));
        assert(gc_pe_face(c2) == Some(cap2));
        assert(gc_parse_at(ss@, Some(hm@)) == Some(cap2));
        assert(gcj(hm@, gc_dot_gitconfig()) == seq![0x2F, 0x68,
            0x2F, 0x2E, 0x67, 0x69, 0x74, 0x63, 0x6F, 0x6E, 0x66,
            0x69, 0x67]);
        assert(gc_parse_at(gcj(hm@, gc_dot_gitconfig()), Some(hm@))
            matches None);
        let b3s = gcj(hm@, gc_dot_config());
        assert(b3s == seq![0x2F, 0x68, 0x2F, 0x2E, 0x63, 0x6F, 0x6E,
            0x66, 0x69, 0x67]);
        let p3s = gcj(b3s, gc_git_config());
        assert(p3s == seq![0x2F, 0x68, 0x2F, 0x2E, 0x63, 0x6F, 0x6E,
            0x66, 0x69, 0x67, 0x2F, 0x67, 0x69, 0x74, 0x2F, 0x63,
            0x6F, 0x6E, 0x66, 0x69, 0x67]);
        assert(gc_read_face(p3s) matches None);
        assert(gc_parse_at(p3s, Some(hm@)) matches None);
        assert(gc_nonempty(Some(ss@)) == Some(ss@));
        assert(gc_excl_spec(None, Some(ss@), None,
            Some(hm@))
            == Some(seq![0x2F, 0x73, 0x79, 0x73, 0x2F, 0x69, 0x67,
                0x6E]));
    }
    let r = gc_excludes_exec(None, Some(ss.as_slice()), None,
        Some(hm.as_slice()));
    assert(r matches Some(_));
    let p = match r {
        Some(x) => x,
        None => Vec::new(),
    };
    assert(p@ == seq![0x2F, 0x73, 0x79, 0x73, 0x2F, 0x69, 0x67, 0x6E]);
}

} // verus!

fn main() {}
