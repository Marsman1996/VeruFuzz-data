//! ignore IG5 **harness zone** -- the dir-stack precedence KAT rows
//! over the src-zone twin (batch IG5: `Ignore::matched` /
//! `matched_ignore` / `matched_dir_entry`, the six-pool fold
//! custom > .ignore > .gitignore > .git/info/exclude > global >
//! explicit, the absolute-parent rewrite seam of dir.rs:625-693 --
//! the 2026-07 fix-wave (issues 3320/3376/3419, PR 3420) -- plus the
//! require_git gate, the saw_git barrier, the errs folds and the
//! builder/resolve/collect faces).
//!
//! Row families (the runtime legs pin every admit: ig5-driver-rows.txt
//! MASK columns quote the same (actual, candidate) pairs):
//! - UT-P: the precedence pairs of dir.rs tests 1176-1344;
//! - UT-B: the saw_git barrier + require_git gate (dir.rs:1395-1416);
//! - UT-A: the absolute-parent rewrite rows (dir.rs:1418-1647 +
//!   tests/misc.rs:749/781, the merged fix-wave regression tests);
//! - UT-C: the hidden dentry tier, the override short-circuit, the
//!   types tier, the global-vs-explicit or-order;
//! - UT-F: builder / resolve / collect faces.
//!
//! Construction style: the store rows construct the matcher stores
//! directly with the ACTUALS the driver rows quote (the driver replays
//! the same geometry through the pinned crate's add_line chain, so
//! the twin's actuals and the runtime actuals agree); every mask
//! admit quotes a driver MASK column.

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/lib.rs"]
mod iglib;

use iglib::dir::{
    any_has_git, append_prefix, collect_ignore_files, dir_matched_spec,
    dir_mi_spec, first_abs, gi_slot_view, ig_any_git,
    ig_has_any_rules_spec, ig_m_view, ig_wf, join_bytes, mi_explicit,
    mi_rewrite, mi_scan, mi_st_none, mi_step, or_hit, strip_keep,
    IgmOrigSpec, IgmPayload, Ignore, IgnoreFilesFound, IgnoreInner,
    IgnoreNode, IgnoreOptions, MiScanSt, ReadOutcome,
    resolve_git_commondir, FsDirEntryFace,
};
use iglib::gitignore::{
    gi_decide, gi_decide_from, gi_decide_from_step, gi_strip_spec,
    Glob as GiGlob, Gitignore, RegisteredGlob, glob_pat_matches,
    globs_field_view, GlobSetFace,
};
use iglib::overrides::Override;
use iglib::pathutil::{bytes_prefix_eq, is_file_name_spec, strip_prefix_spec};
use iglib::types::{FileTypeDef, Selection, Types};
use iglib::{Error, Match, PathBytes};

verus! {

// The Vec push-index bookkeeping (one broadcast per module).
broadcast use vstd::seq::group_seq_axioms;

// =========================================================================
// byte-literal carriers (exact seq posts; driver rows quote the same)
// =========================================================================

/// "foo" (0x66 0x6F 0x6F)
fn b_foo() -> (r: Vec<u8>)
    ensures r@ == seq![0x66, 0x6F, 0x6F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v
}

/// "bar"
fn b_bar() -> (r: Vec<u8>)
    ensures r@ == seq![0x62, 0x61, 0x72]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x62);
    v.push(0x61);
    v.push(0x72);
    v
}

/// "baz"
fn b_baz() -> (r: Vec<u8>)
    ensures r@ == seq![0x62, 0x61, 0x7A]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x62);
    v.push(0x61);
    v.push(0x7A);
    v
}

/// "**/foo" (the add_line rewrite of line "foo")
fn b_ss_foo() -> (r: Vec<u8>)
    ensures r@ == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2A);
    v.push(0x2A);
    v.push(0x2F);
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v
}

/// "**/bar"
fn b_ss_bar() -> (r: Vec<u8>)
    ensures r@ == seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2A);
    v.push(0x2A);
    v.push(0x2F);
    v.push(0x62);
    v.push(0x61);
    v.push(0x72);
    v
}

/// "**/baz"
fn b_ss_baz() -> (r: Vec<u8>)
    ensures r@ == seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x7A]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2A);
    v.push(0x2A);
    v.push(0x2F);
    v.push(0x62);
    v.push(0x61);
    v.push(0x7A);
    v
}

/// "." (the consult special spelling)
fn b_dot() -> (r: Vec<u8>)
    ensures r@ == seq![0x2E]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2E);
    v
}

/// ".hid" (the hidden name spelling; S14 line ".hid" actual "**/.hid")
fn b_hid() -> (r: Vec<u8>)
    ensures r@ == seq![0x2E, 0x68, 0x69, 0x64]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2E);
    v.push(0x68);
    v.push(0x69);
    v.push(0x64);
    v
}

/// "x" (the search-root spelling of the anchored / rules families)
fn b_x() -> (r: Vec<u8>)
    ensures r@ == seq![0x78]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x78);
    v
}

/// "sub" (the search-root spelling of the multi-root families)
fn b_sub() -> (r: Vec<u8>)
    ensures r@ == seq![0x73, 0x75, 0x62]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x73);
    v.push(0x75);
    v.push(0x62);
    v
}

/// "/td" (the parent-root spelling of the absolute families)
fn b_slash_td() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x74, 0x64]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v.push(0x64);
    v
}

/// "/td/foo" (the foo child-of-td spelling)
fn b_slash_td_foo() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v.push(0x64);
    v.push(0x2F);
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v
}

/// "/td/x" (the x root spelling)
fn b_slash_td_x() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x74, 0x64, 0x2F, 0x78]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v.push(0x64);
    v.push(0x2F);
    v.push(0x78);
    v
}

/// "/td/sub" (the sub root spelling)
fn b_slash_td_sub() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75, 0x62]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v.push(0x64);
    v.push(0x2F);
    v.push(0x73);
    v.push(0x75);
    v.push(0x62);
    v
}

/// "x/y/foo" (the three-component candidate spelling; S14 column
/// line="foo" quotes x/y/foo=1)
fn b_x_y_foo() -> (r: Vec<u8>)
    ensures r@ == seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x78);
    v.push(0x2F);
    v.push(0x79);
    v.push(0x2F);
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v
}

/// "y/foo" (the bare spelling of the same file)
fn b_y_foo() -> (r: Vec<u8>)
    ensures r@ == seq![0x79, 0x2F, 0x66, 0x6F, 0x6F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x79);
    v.push(0x2F);
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v
}

/// "x/y/bar" (the three-component miss spelling)
fn b_x_y_bar() -> (r: Vec<u8>)
    ensures r@ == seq![0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x78);
    v.push(0x2F);
    v.push(0x79);
    v.push(0x2F);
    v.push(0x62);
    v.push(0x61);
    v.push(0x72);
    v
}

/// "y/bar" (the bare spelling of the same file)
fn b_y_bar() -> (r: Vec<u8>)
    ensures r@ == seq![0x79, 0x2F, 0x62, 0x61, 0x72]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x79);
    v.push(0x2F);
    v.push(0x62);
    v.push(0x61);
    v.push(0x72);
    v
}

/// "x/y/x.log" (the miss spelling of the rules-through rows)
fn b_x_y_x_log() -> (r: Vec<u8>)
    ensures
        r@ == seq![0x78, 0x2F, 0x79, 0x2F, 0x78, 0x2E, 0x6C, 0x6F,
            0x67]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x78);
    v.push(0x2F);
    v.push(0x79);
    v.push(0x2F);
    v.push(0x78);
    v.push(0x2E);
    v.push(0x6C);
    v.push(0x6F);
    v.push(0x67);
    v
}

/// "y/x.log"
fn b_y_x_log() -> (r: Vec<u8>)
    ensures
        r@ == seq![0x79, 0x2F, 0x78, 0x2E, 0x6C, 0x6F, 0x67]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x79);
    v.push(0x2F);
    v.push(0x78);
    v.push(0x2E);
    v.push(0x6C);
    v.push(0x6F);
    v.push(0x67);
    v
}

/// "sub/x" (the multi-root invalid spelling; S14 column line="sub/**"
/// quotes sub/x=1)
fn b_sub_x() -> (r: Vec<u8>)
    ensures r@ == seq![0x73, 0x75, 0x62, 0x2F, 0x78]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x73);
    v.push(0x75);
    v.push(0x62);
    v.push(0x2F);
    v.push(0x78);
    v
}

/// "foo/x.log" (the multi-root sibling spelling; S14 column
/// line="sub/**" quotes foo/x.log=0)
fn b_foo_x_log() -> (r: Vec<u8>)
    ensures
        r@ == seq![0x66, 0x6F, 0x6F, 0x2F, 0x78, 0x2E, 0x6C, 0x6F,
            0x67]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v.push(0x2F);
    v.push(0x78);
    v.push(0x2E);
    v.push(0x6C);
    v.push(0x6F);
    v.push(0x67);
    v
}

/// "x.log" (the types-tier candidate; S14 column line="*.log" quotes
/// x.log=1 for the rewritten actual "**/*.log")
fn b_x_log() -> (r: Vec<u8>)
    ensures r@ == seq![0x78, 0x2E, 0x6C, 0x6F, 0x67]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x78);
    v.push(0x2E);
    v.push(0x6C);
    v.push(0x6F);
    v.push(0x67);
    v
}

/// "log" (the types def name spelling)
fn b_log() -> (r: Vec<u8>)
    ensures r@ == seq![0x6C, 0x6F, 0x67]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x6C);
    v.push(0x6F);
    v.push(0x67);
    v
}

/// "*.log" (the types def glob spelling)
fn b_star_log() -> (r: Vec<u8>)
    ensures r@ == seq![0x2A, 0x2E, 0x6C, 0x6F, 0x67]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2A);
    v.push(0x2E);
    v.push(0x6C);
    v.push(0x6F);
    v.push(0x67);
    v
}

/// "**/.hid" (the driver actual of the line ".hid")
fn b_ss_hid() -> (r: Vec<u8>)
    ensures r@ == seq![0x2A, 0x2A, 0x2F, 0x2E, 0x68, 0x69, 0x64]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2A);
    v.push(0x2A);
    v.push(0x2F);
    v.push(0x2E);
    v.push(0x68);
    v.push(0x69);
    v.push(0x64);
    v
}

/// "sub/**/*" (the driver actual of the line "sub/**")
fn b_sub_ss() -> (r: Vec<u8>)
    ensures r@ == seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x73);
    v.push(0x75);
    v.push(0x62);
    v.push(0x2F);
    v.push(0x2A);
    v.push(0x2A);
    v.push(0x2F);
    v.push(0x2A);
    v
}

/// "/td/x/foo" (the absolute candidate spelling below the x root)
fn b_slash_td_x_foo() -> (r: Vec<u8>)
    ensures
        r@ == seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x66, 0x6F,
            0x6F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v.push(0x64);
    v.push(0x2F);
    v.push(0x78);
    v.push(0x2F);
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v
}

/// "/td/x/baz" (the absolute candidate spelling below the x root)
fn b_slash_td_x_baz() -> (r: Vec<u8>)
    ensures
        r@ == seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x62, 0x61,
            0x7A]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v.push(0x64);
    v.push(0x2F);
    v.push(0x78);
    v.push(0x2F);
    v.push(0x62);
    v.push(0x61);
    v.push(0x7A);
    v
}

// =========================================================================
// store/stack constructions (direct builder rows; per-index posts)
// =========================================================================

/// One glob entry: actual == original (the driver's actuals), flags
/// given, no source-file binding.
fn h_glob_vec(wl: bool, od: bool, actual: Vec<u8>) -> (r: GiGlob)
    ensures
        r.original@ == actual@,
        r.actual@ == actual@,
        r.is_whitelist == wl,
        r.is_only_dir == od,
        r.from matches None,
{
    GiGlob {
        from: None,
        original: vstd::slice::slice_to_vec(actual.as_slice()),
        actual,
        is_whitelist: wl,
        is_only_dir: od,
    }
}

/// One registered record (no case folding: the gitignore builder
/// default).
fn h_reg_vec(pattern: Vec<u8>) -> (r: RegisteredGlob)
    ensures r.pattern@ == pattern@, !r.case_insensitive
{
    RegisteredGlob { pattern, case_insensitive: false }
}

/// A single-line matcher: root given, one pattern.
fn h_matcher1(
    root: Vec<u8>,
    pat: Vec<u8>,
    wl: bool,
    od: bool,
) -> (r: Gitignore)
    ensures
        r.root.bytes@ == root@,
        r.set.registered@.len() == 1,
        r.globs@.len() == 1,
        r.set.registered@[0].pattern@ == pat@,
        !r.set.registered@[0].case_insensitive,
        r.globs@[0].original@ == pat@,
        r.globs@[0].actual@ == pat@,
        r.globs@[0].is_whitelist == wl,
        r.globs@[0].is_only_dir == od,
        r.globs@[0].from matches None,
        r.num_ignores == (if wl { 0u64 } else { 1u64 }),
        r.num_whitelists == (if wl { 1u64 } else { 0u64 }),
{
    let rr = h_reg_vec(vstd::slice::slice_to_vec(pat.as_slice()));
    let g = h_glob_vec(wl, od, pat);
    let mut regs: Vec<RegisteredGlob> = Vec::new();
    regs.push(rr);
    let mut gs: Vec<GiGlob> = Vec::new();
    gs.push(g);
    Gitignore {
        set: GlobSetFace { registered: regs },
        root: PathBytes { bytes: root },
        globs: gs,
        num_ignores: (if wl { 0u64 } else { 1u64 }),
        num_whitelists: (if wl { 1u64 } else { 0u64 }),
    }
}

/// A two-line matcher: root given, two patterns (higher = later).
/// The FULL per-index component posts (original@ and from at EVERY
/// index): per #IG-19, index instantiation degrades to the literal
/// index axiom, no quantified constructor post layered on top.
fn h_matcher2(
    root: Vec<u8>,
    pat0: Vec<u8>,
    wl0: bool,
    od0: bool,
    pat1: Vec<u8>,
    wl1: bool,
    od1: bool,
) -> (r: Gitignore)
    ensures
        r.root.bytes@ == root@,
        r.set.registered@.len() == 2,
        r.globs@.len() == 2,
        r.set.registered@[0].pattern@ == pat0@,
        r.set.registered@[1].pattern@ == pat1@,
        !r.set.registered@[0].case_insensitive,
        !r.set.registered@[1].case_insensitive,
        r.globs@[0].original@ == pat0@,
        r.globs@[0].actual@ == pat0@,
        r.globs@[0].is_whitelist == wl0,
        r.globs@[0].is_only_dir == od0,
        r.globs@[0].from matches None,
        r.globs@[1].original@ == pat1@,
        r.globs@[1].actual@ == pat1@,
        r.globs@[1].is_whitelist == wl1,
        r.globs@[1].is_only_dir == od1,
        r.globs@[1].from matches None,
        r.num_ignores
            == (if wl0 { 0u64 } else { 1u64 })
                + (if wl1 { 0u64 } else { 1u64 }),
        r.num_whitelists
            == (if wl0 { 1u64 } else { 0u64 })
                + (if wl1 { 1u64 } else { 0u64 }),
{
    let r0 = h_reg_vec(vstd::slice::slice_to_vec(pat0.as_slice()));
    let r1 = h_reg_vec(vstd::slice::slice_to_vec(pat1.as_slice()));
    let g0 = h_glob_vec(wl0, od0, pat0);
    let g1 = h_glob_vec(wl1, od1, pat1);
    let mut regs: Vec<RegisteredGlob> = Vec::new();
    regs.push(r0);
    regs.push(r1);
    let mut gs: Vec<GiGlob> = Vec::new();
    gs.push(g0);
    gs.push(g1);
    Gitignore {
        set: GlobSetFace { registered: regs },
        root: PathBytes { bytes: root },
        globs: gs,
        num_ignores: (if wl0 { 0u64 } else { 1u64 })
            + (if wl1 { 0u64 } else { 1u64 }),
        num_whitelists: (if wl0 { 1u64 } else { 0u64 })
            + (if wl1 { 1u64 } else { 0u64 }),
    }
}



/// The empty matcher (dir.rs Gitignore::empty()).
fn h_empty() -> (r: Gitignore)
    ensures
        r.root.bytes@.len() == 0,
        r.set.registered@.len() == 0,
        r.globs@.len() == 0,
        r.num_ignores == 0,
        r.num_whitelists == 0,
{
    Gitignore {
        set: GlobSetFace { registered: Vec::new() },
        root: PathBytes { bytes: Vec::new() },
        globs: Vec::new(),
        num_ignores: 0,
        num_whitelists: 0,
    }
}

/// The all-bits-default options (the builder head's defaults, the
/// verbatim dir.rs:822-831 table).
fn h_opts_default() -> (r: IgnoreOptions)
    ensures
        r.hidden,
        r.ignore,
        r.parents,
        r.git_global,
        r.git_ignore,
        r.git_exclude,
        !r.ignore_case_insensitive,
        r.require_git,
{
    IgnoreOptions {
        hidden: true,
        ignore: true,
        parents: true,
        git_global: true,
        git_ignore: true,
        git_exclude: true,
        ignore_case_insensitive: false,
        require_git: true,
    }
}

/// Options with require_git off (the gitignore_allowed_no_git tier).
fn h_opts_no_require_git() -> (r: IgnoreOptions)
    ensures
        r.hidden,
        r.ignore,
        r.parents,
        r.git_global,
        r.git_ignore,
        r.git_exclude,
        !r.ignore_case_insensitive,
        !r.require_git,
{
    IgnoreOptions {
        hidden: true,
        ignore: true,
        parents: true,
        git_global: true,
        git_ignore: true,
        git_exclude: true,
        ignore_case_insensitive: false,
        require_git: false,
    }
}

/// The shared ctx: defaults + no explicit list + no global content.
fn h_inner(explicit: Vec<Gitignore>, gg: Gitignore) -> (r: IgnoreInner)
    ensures
        iglib::types::types_wf(&r.types),
        r.opts.hidden,
        r.opts.ignore,
        r.opts.parents,
        r.opts.git_global,
        r.opts.git_ignore,
        r.opts.git_exclude,
        !r.opts.ignore_case_insensitive,
        r.opts.require_git,
        r.explicit_ignores@.len() == explicit.len(),
        forall|k: int| 0 <= k < explicit.len() ==> (
            r.explicit_ignores@[k].root.bytes@
                == explicit@[k].root.bytes@
            && r.explicit_ignores@[k].set.registered@.len()
                == explicit@[k].set.registered@.len()
            && r.explicit_ignores@[k].globs@.len()
                == explicit@[k].globs@.len()
            && r.explicit_ignores@[k].num_ignores
                == explicit@[k].num_ignores
            && r.explicit_ignores@[k].num_whitelists
                == explicit@[k].num_whitelists
            && (forall|j: int| 0 <= j < explicit@[k].globs@.len() ==>
                (globs_field_view(r.explicit_ignores@[k].globs@[j])
                    == globs_field_view(explicit@[k].globs@[j])
                    && r.explicit_ignores@[k].globs@[j].original@
                        == explicit@[k].globs@[j].original@
                    && r.explicit_ignores@[k].globs@[j].actual@
                        == explicit@[k].globs@[j].actual@
                    && r.explicit_ignores@[k].globs@[j].is_whitelist
                        == explicit@[k].globs@[j].is_whitelist
                    && r.explicit_ignores@[k].globs@[j].is_only_dir
                        == explicit@[k].globs@[j].is_only_dir
                    && (match r.explicit_ignores@[k].globs@[j].from {
                        Some(p) => Some(p.bytes@),
                        None => None,
                    } == match explicit@[k].globs@[j].from {
                        Some(p) => Some(p.bytes@),
                        None => None,
                    })))
            && (forall|j: int|
                0 <= j < explicit@[k].set.registered@.len() ==>
                (r.explicit_ignores@[k].set.registered@[j].pattern@
                    == explicit@[k].set.registered@[j].pattern@
                    && r.explicit_ignores@[k].set.registered@[j]
                        .case_insensitive
                        == explicit@[k].set.registered@[j]
                            .case_insensitive))),
        r.git_global_matcher.set.registered@.len()
            == gg.set.registered@.len(),
        r.git_global_matcher.globs@.len() == gg.globs@.len(),
        r.custom_ignore_filenames@.len() == 0,
        r.overrides.inner.set.registered@.len() == 0,
{
    IgnoreInner {
        dir: Vec::new(),
        overrides: Override::empty(),
        types: Types::empty(),
        global_gitignores_relative_to: None,
        explicit_ignores: explicit,
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg,
        opts: IgnoreOptions {
            hidden: true,
            ignore: true,
            parents: true,
            git_global: true,
            git_ignore: true,
            git_exclude: true,
            ignore_case_insensitive: false,
            require_git: true,
        },
    }
}

/// A node with the four per-directory matchers (non-absolute),
/// with full per-index store content posts.
fn h_node_vec(
    dir: Vec<u8>,
    custom: Gitignore,
    ig: Gitignore,
    gi: Gitignore,
    excl: Gitignore,
    has_git: bool,
    has_abs_rules: bool,
) -> (r: IgnoreNode)
    ensures
        r.dir@ == dir@,
        !r.is_absolute_parent,
        r.has_git == has_git,
        r.has_absolute_parent_rules == has_abs_rules,
        r.custom_ignore_matcher.root.bytes@ == custom.root.bytes@,
        r.custom_ignore_matcher.set.registered@.len() == custom.set.registered@.len(),
        r.custom_ignore_matcher.globs@.len() == custom.globs@.len(),
        r.custom_ignore_matcher.num_ignores == custom.num_ignores,
        r.custom_ignore_matcher.num_whitelists == custom.num_whitelists,
        forall|j: int| 0 <= j < custom.globs@.len() ==>
            (globs_field_view(r.custom_ignore_matcher.globs@[j])
                == globs_field_view(custom.globs@[j])
                && r.custom_ignore_matcher.globs@[j].original@
                    == custom.globs@[j].original@
                && r.custom_ignore_matcher.globs@[j].actual@
                    == custom.globs@[j].actual@
                && r.custom_ignore_matcher.globs@[j].is_whitelist
                    == custom.globs@[j].is_whitelist
                && r.custom_ignore_matcher.globs@[j].is_only_dir
                    == custom.globs@[j].is_only_dir),
        forall|j: int| 0 <= j < custom.set.registered@.len() ==>
            (r.custom_ignore_matcher.set.registered@[j].pattern@
                == custom.set.registered@[j].pattern@
                && r.custom_ignore_matcher.set.registered@[j].case_insensitive
                    == custom.set.registered@[j].case_insensitive),
        r.ignore_matcher.root.bytes@ == ig.root.bytes@,
        r.ignore_matcher.set.registered@.len() == ig.set.registered@.len(),
        r.ignore_matcher.globs@.len() == ig.globs@.len(),
        r.ignore_matcher.num_ignores == ig.num_ignores,
        r.ignore_matcher.num_whitelists == ig.num_whitelists,
        forall|j: int| 0 <= j < ig.globs@.len() ==>
            (globs_field_view(r.ignore_matcher.globs@[j])
                == globs_field_view(ig.globs@[j])
                && r.ignore_matcher.globs@[j].original@
                    == ig.globs@[j].original@
                && r.ignore_matcher.globs@[j].actual@
                    == ig.globs@[j].actual@
                && r.ignore_matcher.globs@[j].is_whitelist
                    == ig.globs@[j].is_whitelist
                && r.ignore_matcher.globs@[j].is_only_dir
                    == ig.globs@[j].is_only_dir),
        forall|j: int| 0 <= j < ig.set.registered@.len() ==>
            (r.ignore_matcher.set.registered@[j].pattern@
                == ig.set.registered@[j].pattern@
                && r.ignore_matcher.set.registered@[j].case_insensitive
                    == ig.set.registered@[j].case_insensitive),
        r.git_ignore_matcher.root.bytes@ == gi.root.bytes@,
        r.git_ignore_matcher.set.registered@.len() == gi.set.registered@.len(),
        r.git_ignore_matcher.globs@.len() == gi.globs@.len(),
        r.git_ignore_matcher.num_ignores == gi.num_ignores,
        r.git_ignore_matcher.num_whitelists == gi.num_whitelists,
        forall|j: int| 0 <= j < gi.globs@.len() ==>
            (globs_field_view(r.git_ignore_matcher.globs@[j])
                == globs_field_view(gi.globs@[j])
                && r.git_ignore_matcher.globs@[j].original@
                    == gi.globs@[j].original@
                && r.git_ignore_matcher.globs@[j].actual@
                    == gi.globs@[j].actual@
                && r.git_ignore_matcher.globs@[j].is_whitelist
                    == gi.globs@[j].is_whitelist
                && r.git_ignore_matcher.globs@[j].is_only_dir
                    == gi.globs@[j].is_only_dir),
        forall|j: int| 0 <= j < gi.set.registered@.len() ==>
            (r.git_ignore_matcher.set.registered@[j].pattern@
                == gi.set.registered@[j].pattern@
                && r.git_ignore_matcher.set.registered@[j].case_insensitive
                    == gi.set.registered@[j].case_insensitive),
        r.git_exclude_matcher.root.bytes@ == excl.root.bytes@,
        r.git_exclude_matcher.set.registered@.len() == excl.set.registered@.len(),
        r.git_exclude_matcher.globs@.len() == excl.globs@.len(),
        r.git_exclude_matcher.num_ignores == excl.num_ignores,
        r.git_exclude_matcher.num_whitelists == excl.num_whitelists,
        forall|j: int| 0 <= j < excl.globs@.len() ==>
            (globs_field_view(r.git_exclude_matcher.globs@[j])
                == globs_field_view(excl.globs@[j])
                && r.git_exclude_matcher.globs@[j].original@
                    == excl.globs@[j].original@
                && r.git_exclude_matcher.globs@[j].actual@
                    == excl.globs@[j].actual@
                && r.git_exclude_matcher.globs@[j].is_whitelist
                    == excl.globs@[j].is_whitelist
                && r.git_exclude_matcher.globs@[j].is_only_dir
                    == excl.globs@[j].is_only_dir),
        forall|j: int| 0 <= j < excl.set.registered@.len() ==>
            (r.git_exclude_matcher.set.registered@[j].pattern@
                == excl.set.registered@[j].pattern@
                && r.git_exclude_matcher.set.registered@[j].case_insensitive
                    == excl.set.registered@[j].case_insensitive),
{
    IgnoreNode {
        dir,
        is_absolute_parent: false,
        has_absolute_parent_rules: has_abs_rules,
        has_git,
        custom_ignore_matcher: custom,
        ignore_matcher: ig,
        git_ignore_matcher: gi,
        git_exclude_matcher: excl,
    }
}

/// The builder-root tail node (empty matchers, absolute).
fn h_root_node() -> (r: IgnoreNode)
    ensures
        r.is_absolute_parent,
        !r.has_git,
        !r.has_absolute_parent_rules,
        r.custom_ignore_matcher.set.registered@.len() == 0,
        r.ignore_matcher.set.registered@.len() == 0,
        r.git_ignore_matcher.set.registered@.len() == 0,
        r.git_exclude_matcher.set.registered@.len() == 0,
{
    IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    }
}

/// A two-node stack: one relative head + the builder root (full per-index content posts).
fn h_stack2(
    inner: IgnoreInner,
    head: IgnoreNode,
    abs_base: Option<Vec<u8>>,
) -> (r: Ignore)
    requires
        iglib::types::types_wf(&inner.types),
        !head.is_absolute_parent,
    ensures
        iglib::dir::ig_shape(r.nodes@),
        iglib::types::types_wf(&r.inner.types),
        !r.nodes@[0].is_absolute_parent,
        r.nodes@.len() == 2,
        r.nodes@[0].dir@ == head.dir@,
        r.nodes@[0].has_git == head.has_git,
        r.nodes@[0].has_absolute_parent_rules
            == head.has_absolute_parent_rules,
        r.nodes@[1].is_absolute_parent,
        r.nodes@[1].has_git == false,
        r.nodes@[1].has_absolute_parent_rules == false,
        r.nodes@[1].custom_ignore_matcher.set.registered@.len() == 0,
        r.nodes@[1].ignore_matcher.set.registered@.len() == 0,
        r.nodes@[1].git_ignore_matcher.set.registered@.len() == 0,
        r.nodes@[1].git_exclude_matcher.set.registered@.len() == 0,
        r.absolute_base@ == abs_base@,
        r.inner.opts.hidden == inner.opts.hidden,
        r.inner.opts.ignore == inner.opts.ignore,
        r.inner.opts.parents == inner.opts.parents,
        r.inner.opts.git_global == inner.opts.git_global,
        r.inner.opts.git_ignore == inner.opts.git_ignore,
        r.inner.opts.git_exclude == inner.opts.git_exclude,
        r.inner.opts.require_git == inner.opts.require_git,
        r.inner.explicit_ignores@.len() == inner.explicit_ignores@.len(),
        r.inner.custom_ignore_filenames@.len()
            == inner.custom_ignore_filenames@.len(),
        r.inner.overrides.inner.set.registered@.len()
            == inner.overrides.inner.set.registered@.len(),

        r.nodes@[0].custom_ignore_matcher.root.bytes@ == head.custom_ignore_matcher.root.bytes@,
        r.nodes@[0].custom_ignore_matcher.set.registered@.len() == head.custom_ignore_matcher.set.registered@.len(),
        r.nodes@[0].custom_ignore_matcher.globs@.len() == head.custom_ignore_matcher.globs@.len(),
        r.nodes@[0].custom_ignore_matcher.num_ignores == head.custom_ignore_matcher.num_ignores,
        r.nodes@[0].custom_ignore_matcher.num_whitelists == head.custom_ignore_matcher.num_whitelists,
        forall|j: int| 0 <= j < head.custom_ignore_matcher.globs@.len() ==>
            (globs_field_view(r.nodes@[0].custom_ignore_matcher.globs@[j])
                == globs_field_view(head.custom_ignore_matcher.globs@[j])),
        forall|j: int| 0 <= j < head.custom_ignore_matcher.set.registered@.len() ==>
            (r.nodes@[0].custom_ignore_matcher.set.registered@[j].pattern@
                == head.custom_ignore_matcher.set.registered@[j].pattern@
                && r.nodes@[0].custom_ignore_matcher.set.registered@[j].case_insensitive
                    == head.custom_ignore_matcher.set.registered@[j].case_insensitive),
        r.nodes@[0].ignore_matcher.root.bytes@ == head.ignore_matcher.root.bytes@,
        r.nodes@[0].ignore_matcher.set.registered@.len() == head.ignore_matcher.set.registered@.len(),
        r.nodes@[0].ignore_matcher.globs@.len() == head.ignore_matcher.globs@.len(),
        r.nodes@[0].ignore_matcher.num_ignores == head.ignore_matcher.num_ignores,
        r.nodes@[0].ignore_matcher.num_whitelists == head.ignore_matcher.num_whitelists,
        forall|j: int| 0 <= j < head.ignore_matcher.globs@.len() ==>
            (globs_field_view(r.nodes@[0].ignore_matcher.globs@[j])
                == globs_field_view(head.ignore_matcher.globs@[j])),
        forall|j: int| 0 <= j < head.ignore_matcher.set.registered@.len() ==>
            (r.nodes@[0].ignore_matcher.set.registered@[j].pattern@
                == head.ignore_matcher.set.registered@[j].pattern@
                && r.nodes@[0].ignore_matcher.set.registered@[j].case_insensitive
                    == head.ignore_matcher.set.registered@[j].case_insensitive),
        r.nodes@[0].git_ignore_matcher.root.bytes@ == head.git_ignore_matcher.root.bytes@,
        r.nodes@[0].git_ignore_matcher.set.registered@.len() == head.git_ignore_matcher.set.registered@.len(),
        r.nodes@[0].git_ignore_matcher.globs@.len() == head.git_ignore_matcher.globs@.len(),
        r.nodes@[0].git_ignore_matcher.num_ignores == head.git_ignore_matcher.num_ignores,
        r.nodes@[0].git_ignore_matcher.num_whitelists == head.git_ignore_matcher.num_whitelists,
        forall|j: int| 0 <= j < head.git_ignore_matcher.globs@.len() ==>
            (globs_field_view(r.nodes@[0].git_ignore_matcher.globs@[j])
                == globs_field_view(head.git_ignore_matcher.globs@[j])),
        forall|j: int| 0 <= j < head.git_ignore_matcher.set.registered@.len() ==>
            (r.nodes@[0].git_ignore_matcher.set.registered@[j].pattern@
                == head.git_ignore_matcher.set.registered@[j].pattern@
                && r.nodes@[0].git_ignore_matcher.set.registered@[j].case_insensitive
                    == head.git_ignore_matcher.set.registered@[j].case_insensitive),
        r.nodes@[0].git_exclude_matcher.root.bytes@ == head.git_exclude_matcher.root.bytes@,
        r.nodes@[0].git_exclude_matcher.set.registered@.len() == head.git_exclude_matcher.set.registered@.len(),
        r.nodes@[0].git_exclude_matcher.globs@.len() == head.git_exclude_matcher.globs@.len(),
        r.nodes@[0].git_exclude_matcher.num_ignores == head.git_exclude_matcher.num_ignores,
        r.nodes@[0].git_exclude_matcher.num_whitelists == head.git_exclude_matcher.num_whitelists,
        forall|j: int| 0 <= j < head.git_exclude_matcher.globs@.len() ==>
            (globs_field_view(r.nodes@[0].git_exclude_matcher.globs@[j])
                == globs_field_view(head.git_exclude_matcher.globs@[j])),
        forall|j: int| 0 <= j < head.git_exclude_matcher.set.registered@.len() ==>
            (r.nodes@[0].git_exclude_matcher.set.registered@[j].pattern@
                == head.git_exclude_matcher.set.registered@[j].pattern@
                && r.nodes@[0].git_exclude_matcher.set.registered@[j].case_insensitive
                    == head.git_exclude_matcher.set.registered@[j].case_insensitive),
        forall|k: int| 0 <= k < inner.explicit_ignores@.len() ==> (
            r.inner.explicit_ignores@[k].root.bytes@
                == inner.explicit_ignores@[k].root.bytes@
            && r.inner.explicit_ignores@[k].set.registered@.len()
                == inner.explicit_ignores@[k].set.registered@.len()
            && r.inner.explicit_ignores@[k].globs@.len()
                == inner.explicit_ignores@[k].globs@.len()
            && (forall|j: int|
                0 <= j < inner.explicit_ignores@[k].globs@.len() ==>
                (globs_field_view(r.inner.explicit_ignores@[k].globs@[j])
                    == globs_field_view(
                        inner.explicit_ignores@[k].globs@[j])
                    && r.inner.explicit_ignores@[k].globs@[j].original@
                        == inner.explicit_ignores@[k].globs@[j].original@
                    && r.inner.explicit_ignores@[k].globs@[j].actual@
                        == inner.explicit_ignores@[k].globs@[j].actual@
                    && r.inner.explicit_ignores@[k].globs@[j].is_whitelist
                        == inner.explicit_ignores@[k].globs@[j]
                            .is_whitelist
                    && r.inner.explicit_ignores@[k].globs@[j].is_only_dir
                        == inner.explicit_ignores@[k].globs@[j]
                            .is_only_dir
                    && (match r.inner.explicit_ignores@[k].globs@[j]
                        .from {
                        Some(p) => Some(p.bytes@),
                        None => None,
                    } == match inner.explicit_ignores@[k].globs@[j].from {
                        Some(p) => Some(p.bytes@),
                        None => None,
                    })))
            && (forall|j: int|
                0 <= j < inner.explicit_ignores@[k]
                    .set.registered@.len() ==>
                (r.inner.explicit_ignores@[k].set.registered@[j]
                        .pattern@
                    == inner.explicit_ignores@[k]
                        .set.registered@[j].pattern@
                    && r.inner.explicit_ignores@[k].set
                        .registered@[j].case_insensitive
                        == inner.explicit_ignores@[k].set.registered@[j]
                            .case_insensitive))),
        r.inner.git_global_matcher.root.bytes@
            == inner.git_global_matcher.root.bytes@,
        r.inner.git_global_matcher.set.registered@.len()
            == inner.git_global_matcher.set.registered@.len(),
        r.inner.git_global_matcher.globs@.len()
            == inner.git_global_matcher.globs@.len(),
        forall|j: int| 0 <= j < inner.git_global_matcher.globs@.len() ==>
            (globs_field_view(r.inner.git_global_matcher.globs@[j])
                == globs_field_view(inner.git_global_matcher.globs@[j])),
        forall|j: int|
            0 <= j < inner.git_global_matcher.set.registered@.len() ==>
            (r.inner.git_global_matcher.set.registered@[j].pattern@
                == inner.git_global_matcher.set.registered@[j].pattern@),
{
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    let root = h_root_node();
    ns.push(root);
    proof {
        assert(root.is_absolute_parent);
        assert(ns@.len() == 2);
        assert(iglib::dir::ig_shape(ns@));
    }
    Ignore { inner, nodes: ns, absolute_base: abs_base }
}

/// A three-node stack: two relative heads + the builder root (full per-index content posts).
fn h_stack3(
    inner: IgnoreInner,
    head: IgnoreNode,
    mid: IgnoreNode,
    abs_base: Option<Vec<u8>>,
) -> (r: Ignore)
    requires
        iglib::types::types_wf(&inner.types),
        !head.is_absolute_parent,
        !mid.is_absolute_parent,
    ensures
        iglib::dir::ig_shape(r.nodes@),
        iglib::types::types_wf(&r.inner.types),
        !r.nodes@[0].is_absolute_parent,
        !r.nodes@[1].is_absolute_parent,
        r.nodes@.len() == 3,
        r.nodes@[0].dir@ == head.dir@,
        r.nodes@[0].has_git == head.has_git,
        r.nodes@[0].has_absolute_parent_rules
            == head.has_absolute_parent_rules,
        r.nodes@[1].dir@ == mid.dir@,
        r.nodes@[1].has_git == mid.has_git,
        r.nodes@[1].has_absolute_parent_rules
            == mid.has_absolute_parent_rules,
        r.nodes@[2].is_absolute_parent,
        r.nodes@[2].has_git == false,
        r.nodes@[2].has_absolute_parent_rules == false,
        r.nodes@[2].custom_ignore_matcher.set.registered@.len() == 0,
        r.nodes@[2].ignore_matcher.set.registered@.len() == 0,
        r.nodes@[2].git_ignore_matcher.set.registered@.len() == 0,
        r.nodes@[2].git_exclude_matcher.set.registered@.len() == 0,
        r.absolute_base@ == abs_base@,
        r.inner.opts.hidden == inner.opts.hidden,
        r.inner.opts.ignore == inner.opts.ignore,
        r.inner.opts.parents == inner.opts.parents,
        r.inner.opts.git_global == inner.opts.git_global,
        r.inner.opts.git_ignore == inner.opts.git_ignore,
        r.inner.opts.git_exclude == inner.opts.git_exclude,
        r.inner.opts.require_git == inner.opts.require_git,
        r.inner.explicit_ignores@.len() == inner.explicit_ignores@.len(),
        r.inner.custom_ignore_filenames@.len()
            == inner.custom_ignore_filenames@.len(),
        r.inner.overrides.inner.set.registered@.len()
            == inner.overrides.inner.set.registered@.len(),

        r.nodes@[0].custom_ignore_matcher.root.bytes@ == head.custom_ignore_matcher.root.bytes@,
        r.nodes@[0].custom_ignore_matcher.set.registered@.len() == head.custom_ignore_matcher.set.registered@.len(),
        r.nodes@[0].custom_ignore_matcher.globs@.len() == head.custom_ignore_matcher.globs@.len(),
        r.nodes@[0].custom_ignore_matcher.num_ignores == head.custom_ignore_matcher.num_ignores,
        r.nodes@[0].custom_ignore_matcher.num_whitelists == head.custom_ignore_matcher.num_whitelists,
        forall|j: int| 0 <= j < head.custom_ignore_matcher.globs@.len() ==>
            (globs_field_view(r.nodes@[0].custom_ignore_matcher.globs@[j])
                == globs_field_view(head.custom_ignore_matcher.globs@[j])),
        forall|j: int| 0 <= j < head.custom_ignore_matcher.set.registered@.len() ==>
            (r.nodes@[0].custom_ignore_matcher.set.registered@[j].pattern@
                == head.custom_ignore_matcher.set.registered@[j].pattern@
                && r.nodes@[0].custom_ignore_matcher.set.registered@[j].case_insensitive
                    == head.custom_ignore_matcher.set.registered@[j].case_insensitive),
        r.nodes@[0].ignore_matcher.root.bytes@ == head.ignore_matcher.root.bytes@,
        r.nodes@[0].ignore_matcher.set.registered@.len() == head.ignore_matcher.set.registered@.len(),
        r.nodes@[0].ignore_matcher.globs@.len() == head.ignore_matcher.globs@.len(),
        r.nodes@[0].ignore_matcher.num_ignores == head.ignore_matcher.num_ignores,
        r.nodes@[0].ignore_matcher.num_whitelists == head.ignore_matcher.num_whitelists,
        forall|j: int| 0 <= j < head.ignore_matcher.globs@.len() ==>
            (globs_field_view(r.nodes@[0].ignore_matcher.globs@[j])
                == globs_field_view(head.ignore_matcher.globs@[j])),
        forall|j: int| 0 <= j < head.ignore_matcher.set.registered@.len() ==>
            (r.nodes@[0].ignore_matcher.set.registered@[j].pattern@
                == head.ignore_matcher.set.registered@[j].pattern@
                && r.nodes@[0].ignore_matcher.set.registered@[j].case_insensitive
                    == head.ignore_matcher.set.registered@[j].case_insensitive),
        r.nodes@[0].git_ignore_matcher.root.bytes@ == head.git_ignore_matcher.root.bytes@,
        r.nodes@[0].git_ignore_matcher.set.registered@.len() == head.git_ignore_matcher.set.registered@.len(),
        r.nodes@[0].git_ignore_matcher.globs@.len() == head.git_ignore_matcher.globs@.len(),
        r.nodes@[0].git_ignore_matcher.num_ignores == head.git_ignore_matcher.num_ignores,
        r.nodes@[0].git_ignore_matcher.num_whitelists == head.git_ignore_matcher.num_whitelists,
        forall|j: int| 0 <= j < head.git_ignore_matcher.globs@.len() ==>
            (globs_field_view(r.nodes@[0].git_ignore_matcher.globs@[j])
                == globs_field_view(head.git_ignore_matcher.globs@[j])),
        forall|j: int| 0 <= j < head.git_ignore_matcher.set.registered@.len() ==>
            (r.nodes@[0].git_ignore_matcher.set.registered@[j].pattern@
                == head.git_ignore_matcher.set.registered@[j].pattern@
                && r.nodes@[0].git_ignore_matcher.set.registered@[j].case_insensitive
                    == head.git_ignore_matcher.set.registered@[j].case_insensitive),
        r.nodes@[0].git_exclude_matcher.root.bytes@ == head.git_exclude_matcher.root.bytes@,
        r.nodes@[0].git_exclude_matcher.set.registered@.len() == head.git_exclude_matcher.set.registered@.len(),
        r.nodes@[0].git_exclude_matcher.globs@.len() == head.git_exclude_matcher.globs@.len(),
        r.nodes@[0].git_exclude_matcher.num_ignores == head.git_exclude_matcher.num_ignores,
        r.nodes@[0].git_exclude_matcher.num_whitelists == head.git_exclude_matcher.num_whitelists,
        forall|j: int| 0 <= j < head.git_exclude_matcher.globs@.len() ==>
            (globs_field_view(r.nodes@[0].git_exclude_matcher.globs@[j])
                == globs_field_view(head.git_exclude_matcher.globs@[j])),
        forall|j: int| 0 <= j < head.git_exclude_matcher.set.registered@.len() ==>
            (r.nodes@[0].git_exclude_matcher.set.registered@[j].pattern@
                == head.git_exclude_matcher.set.registered@[j].pattern@
                && r.nodes@[0].git_exclude_matcher.set.registered@[j].case_insensitive
                    == head.git_exclude_matcher.set.registered@[j].case_insensitive),
        r.nodes@[1].custom_ignore_matcher.root.bytes@ == mid.custom_ignore_matcher.root.bytes@,
        r.nodes@[1].custom_ignore_matcher.set.registered@.len() == mid.custom_ignore_matcher.set.registered@.len(),
        r.nodes@[1].custom_ignore_matcher.globs@.len() == mid.custom_ignore_matcher.globs@.len(),
        r.nodes@[1].custom_ignore_matcher.num_ignores == mid.custom_ignore_matcher.num_ignores,
        r.nodes@[1].custom_ignore_matcher.num_whitelists == mid.custom_ignore_matcher.num_whitelists,
        forall|j: int| 0 <= j < mid.custom_ignore_matcher.globs@.len() ==>
            (globs_field_view(r.nodes@[1].custom_ignore_matcher.globs@[j])
                == globs_field_view(mid.custom_ignore_matcher.globs@[j])),
        forall|j: int| 0 <= j < mid.custom_ignore_matcher.set.registered@.len() ==>
            (r.nodes@[1].custom_ignore_matcher.set.registered@[j].pattern@
                == mid.custom_ignore_matcher.set.registered@[j].pattern@
                && r.nodes@[1].custom_ignore_matcher.set.registered@[j].case_insensitive
                    == mid.custom_ignore_matcher.set.registered@[j].case_insensitive),
        r.nodes@[1].ignore_matcher.root.bytes@ == mid.ignore_matcher.root.bytes@,
        r.nodes@[1].ignore_matcher.set.registered@.len() == mid.ignore_matcher.set.registered@.len(),
        r.nodes@[1].ignore_matcher.globs@.len() == mid.ignore_matcher.globs@.len(),
        r.nodes@[1].ignore_matcher.num_ignores == mid.ignore_matcher.num_ignores,
        r.nodes@[1].ignore_matcher.num_whitelists == mid.ignore_matcher.num_whitelists,
        forall|j: int| 0 <= j < mid.ignore_matcher.globs@.len() ==>
            (globs_field_view(r.nodes@[1].ignore_matcher.globs@[j])
                == globs_field_view(mid.ignore_matcher.globs@[j])),
        forall|j: int| 0 <= j < mid.ignore_matcher.set.registered@.len() ==>
            (r.nodes@[1].ignore_matcher.set.registered@[j].pattern@
                == mid.ignore_matcher.set.registered@[j].pattern@
                && r.nodes@[1].ignore_matcher.set.registered@[j].case_insensitive
                    == mid.ignore_matcher.set.registered@[j].case_insensitive),
        r.nodes@[1].git_ignore_matcher.root.bytes@ == mid.git_ignore_matcher.root.bytes@,
        r.nodes@[1].git_ignore_matcher.set.registered@.len() == mid.git_ignore_matcher.set.registered@.len(),
        r.nodes@[1].git_ignore_matcher.globs@.len() == mid.git_ignore_matcher.globs@.len(),
        r.nodes@[1].git_ignore_matcher.num_ignores == mid.git_ignore_matcher.num_ignores,
        r.nodes@[1].git_ignore_matcher.num_whitelists == mid.git_ignore_matcher.num_whitelists,
        forall|j: int| 0 <= j < mid.git_ignore_matcher.globs@.len() ==>
            (globs_field_view(r.nodes@[1].git_ignore_matcher.globs@[j])
                == globs_field_view(mid.git_ignore_matcher.globs@[j])),
        forall|j: int| 0 <= j < mid.git_ignore_matcher.set.registered@.len() ==>
            (r.nodes@[1].git_ignore_matcher.set.registered@[j].pattern@
                == mid.git_ignore_matcher.set.registered@[j].pattern@
                && r.nodes@[1].git_ignore_matcher.set.registered@[j].case_insensitive
                    == mid.git_ignore_matcher.set.registered@[j].case_insensitive),
        r.nodes@[1].git_exclude_matcher.root.bytes@ == mid.git_exclude_matcher.root.bytes@,
        r.nodes@[1].git_exclude_matcher.set.registered@.len() == mid.git_exclude_matcher.set.registered@.len(),
        r.nodes@[1].git_exclude_matcher.globs@.len() == mid.git_exclude_matcher.globs@.len(),
        r.nodes@[1].git_exclude_matcher.num_ignores == mid.git_exclude_matcher.num_ignores,
        r.nodes@[1].git_exclude_matcher.num_whitelists == mid.git_exclude_matcher.num_whitelists,
        forall|j: int| 0 <= j < mid.git_exclude_matcher.globs@.len() ==>
            (globs_field_view(r.nodes@[1].git_exclude_matcher.globs@[j])
                == globs_field_view(mid.git_exclude_matcher.globs@[j])),
        forall|j: int| 0 <= j < mid.git_exclude_matcher.set.registered@.len() ==>
            (r.nodes@[1].git_exclude_matcher.set.registered@[j].pattern@
                == mid.git_exclude_matcher.set.registered@[j].pattern@
                && r.nodes@[1].git_exclude_matcher.set.registered@[j].case_insensitive
                    == mid.git_exclude_matcher.set.registered@[j].case_insensitive),
        forall|k: int| 0 <= k < inner.explicit_ignores@.len() ==> (
            r.inner.explicit_ignores@[k].root.bytes@
                == inner.explicit_ignores@[k].root.bytes@
            && r.inner.explicit_ignores@[k].set.registered@.len()
                == inner.explicit_ignores@[k].set.registered@.len()
            && r.inner.explicit_ignores@[k].globs@.len()
                == inner.explicit_ignores@[k].globs@.len()
            && (forall|j: int|
                0 <= j < inner.explicit_ignores@[k].globs@.len() ==>
                (globs_field_view(r.inner.explicit_ignores@[k].globs@[j])
                    == globs_field_view(
                        inner.explicit_ignores@[k].globs@[j])
                    && r.inner.explicit_ignores@[k].globs@[j].original@
                        == inner.explicit_ignores@[k].globs@[j].original@
                    && r.inner.explicit_ignores@[k].globs@[j].actual@
                        == inner.explicit_ignores@[k].globs@[j].actual@
                    && r.inner.explicit_ignores@[k].globs@[j].is_whitelist
                        == inner.explicit_ignores@[k].globs@[j]
                            .is_whitelist
                    && r.inner.explicit_ignores@[k].globs@[j].is_only_dir
                        == inner.explicit_ignores@[k].globs@[j]
                            .is_only_dir
                    && (match r.inner.explicit_ignores@[k].globs@[j]
                        .from {
                        Some(p) => Some(p.bytes@),
                        None => None,
                    } == match inner.explicit_ignores@[k].globs@[j].from {
                        Some(p) => Some(p.bytes@),
                        None => None,
                    })))
            && (forall|j: int|
                0 <= j < inner.explicit_ignores@[k]
                    .set.registered@.len() ==>
                (r.inner.explicit_ignores@[k].set.registered@[j]
                        .pattern@
                    == inner.explicit_ignores@[k]
                        .set.registered@[j].pattern@
                    && r.inner.explicit_ignores@[k].set
                        .registered@[j].case_insensitive
                        == inner.explicit_ignores@[k].set.registered@[j]
                            .case_insensitive))),
        r.inner.git_global_matcher.root.bytes@
            == inner.git_global_matcher.root.bytes@,
        r.inner.git_global_matcher.set.registered@.len()
            == inner.git_global_matcher.set.registered@.len(),
        r.inner.git_global_matcher.globs@.len()
            == inner.git_global_matcher.globs@.len(),
        forall|j: int| 0 <= j < inner.git_global_matcher.globs@.len() ==>
            (globs_field_view(r.inner.git_global_matcher.globs@[j])
                == globs_field_view(inner.git_global_matcher.globs@[j])),
        forall|j: int|
            0 <= j < inner.git_global_matcher.set.registered@.len() ==>
            (r.inner.git_global_matcher.set.registered@[j].pattern@
                == inner.git_global_matcher.set.registered@[j].pattern@),
{
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(mid);
    let root = h_root_node();
    ns.push(root);
    proof {
        assert(root.is_absolute_parent);
        assert(ns@.len() == 3);
        assert(iglib::dir::ig_shape(ns@));
    }
    Ignore { inner, nodes: ns, absolute_base: abs_base }
}




/// "/t/td" (the td root spelling)
fn b_td_root() -> (r: Vec<u8>)
    ensures
        r@ == seq![0x2F, 0x74, 0x2F, 0x74, 0x64]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v.push(0x2F);
    v.push(0x74);
    v.push(0x64);
    v
}

/// "td" (the bare dir spelling)
fn b_td() -> (r: Vec<u8>)
    ensures r@ == seq![0x74, 0x64]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x74);
    v.push(0x64);
    v
}

/// ".customignore"
fn b_xcustom() -> (r: Vec<u8>)
    ensures
        r@ == seq![0x2E, 0x63, 0x75, 0x73, 0x74, 0x6F, 0x6D, 0x69,
            0x67, 0x6E, 0x6F, 0x72, 0x65]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2E);
    v.push(0x63);
    v.push(0x75);
    v.push(0x73);
    v.push(0x74);
    v.push(0x6F);
    v.push(0x6D);
    v.push(0x69);
    v.push(0x67);
    v.push(0x6E);
    v.push(0x6F);
    v.push(0x72);
    v.push(0x65);
    v
}

/// The ctx with require_git off.
fn h_inner_opts_no_git(
    explicit: Vec<Gitignore>,
    gg: Gitignore,
) -> (r: IgnoreInner)
    ensures
        iglib::types::types_wf(&r.types),
        r.opts.hidden,
        r.opts.ignore,
        r.opts.parents,
        r.opts.git_global,
        r.opts.git_ignore,
        r.opts.git_exclude,
        !r.opts.ignore_case_insensitive,
        !r.opts.require_git,
        r.explicit_ignores@.len() == explicit.len(),
        r.git_global_matcher.set.registered@.len()
            == gg.set.registered@.len(),
        r.git_global_matcher.globs@.len() == gg.globs@.len(),
        r.custom_ignore_filenames@.len() == 0,
        r.overrides.inner.set.registered@.len() == 0,
{
    IgnoreInner {
        dir: Vec::new(),
        overrides: Override::empty(),
        types: Types::empty(),
        global_gitignores_relative_to: None,
        explicit_ignores: explicit,
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg,
        opts: h_opts_no_require_git(),
    }
}

/// The ctx carrying custom ignore filenames.
fn h_inner_custom(
    names: Vec<Vec<u8>>,
    explicit: Vec<Gitignore>,
    gg: Gitignore,
) -> (r: IgnoreInner)
    ensures
        iglib::types::types_wf(&r.types),
        r.opts.hidden,
        r.opts.ignore,
        r.opts.parents,
        r.opts.git_global,
        r.opts.git_ignore,
        r.opts.git_exclude,
        !r.opts.ignore_case_insensitive,
        r.opts.require_git,
        r.explicit_ignores@.len() == explicit.len(),
        r.custom_ignore_filenames@.len() == names.len(),
        r.overrides.inner.set.registered@.len() == 0,
{
    IgnoreInner {
        dir: Vec::new(),
        overrides: Override::empty(),
        types: Types::empty(),
        global_gitignores_relative_to: None,
        explicit_ignores: explicit,
        custom_ignore_filenames: names,
        git_global_matcher: gg,
        opts: h_opts_default(),
    }
}

// =========================================================================
// the slot-evaluation helpers (the rung machinery: empty stores
// decide None; a one-line store decides per the mask admit)
// =========================================================================

/// Empty stores decide None (gi_decide bottoms out below zero).
proof fn gi_slot_empty_eval(
    globs: Seq<GiGlob>,
    registered: Seq<RegisteredGlob>,
    root: Seq<u8>,
    path: Seq<u8>,
    is_dir: bool,
)
    requires globs.len() == 0, registered.len() == 0
    ensures gi_slot_view(globs, registered, root, path, is_dir) == None
{
    reveal(gi_slot_view);
    reveal(gi_decide);
    reveal_with_fuel(gi_decide_from, 2);
    assert(gi_decide(globs, registered, path, is_dir) matches None);
}

/// A one-line store decides: the masked hit element's field view rides
/// the Gi arm (whitelist flag and only_dir gate per the row's store).
proof fn gi_slot_one_eval(
    globs: Seq<GiGlob>,
    registered: Seq<RegisteredGlob>,
    root: Seq<u8>,
    path: Seq<u8>,
    is_dir: bool,
    strip: Seq<u8>,
    wl: bool,
    od: bool,
    orig: Seq<u8>,
    actual: Seq<u8>,
)
    requires
        globs.len() == 1,
        registered.len() == 1,
        registered[0].pattern@ == actual,
        !registered[0].case_insensitive,
        globs[0].original@ == orig,
        globs[0].actual@ == actual,
        globs[0].is_whitelist == wl,
        globs[0].is_only_dir == od,
        globs[0].from matches None,
        (od ==> is_dir),
        gi_strip_spec(root, path) == strip,
        glob_pat_matches(actual, false, strip),
    ensures
        gi_slot_view(globs, registered, root, path, is_dir)
            == Some((wl, IgmOrigSpec::Gi((orig, actual, wl, od,
                match globs[0].from {
                    Some(p) => Some(p.bytes@),
                    None => None,
                }))))
{
    reveal(gi_slot_view);
    reveal(gi_decide);
    reveal_with_fuel(gi_decide_from, 2);
    gi_decide_from_step(globs, registered, gi_strip_spec(root, path),
        is_dir, 0);
    assert(gi_decide_from(globs, registered, gi_strip_spec(root, path),
        is_dir, 0) == Some((wl, 0)));
}

/// A one-line MISSED store: the pattern passes the mask admit as
/// false, so the store decides None.
proof fn gi_slot_one_miss(
    globs: Seq<GiGlob>,
    registered: Seq<RegisteredGlob>,
    root: Seq<u8>,
    path: Seq<u8>,
    is_dir: bool,
    strip: Seq<u8>,
    actual: Seq<u8>,
)
    requires
        globs.len() == 1,
        registered.len() == 1,
        registered[0].pattern@ == actual,
        !registered[0].case_insensitive,
        (globs[0].is_only_dir ==> is_dir),
        gi_strip_spec(root, path) == strip,
        !glob_pat_matches(actual, false, strip),
    ensures gi_slot_view(globs, registered, root, path, is_dir) == None
{
    reveal(gi_slot_view);
    reveal(gi_decide);
    reveal_with_fuel(gi_decide_from, 2);
    gi_decide_from_step(globs, registered, gi_strip_spec(root, path),
        is_dir, 0);
    assert(gi_decide_from(globs, registered, gi_strip_spec(root, path),
        is_dir, 0) matches None);
}

/// A two-line store with the LOWER index masked-out and the HIGHER
/// index the hit (the "later names have higher precedence" face, the
/// reversed-scan semantics of dir.rs:694-699 / the per-file order).
proof fn gi_slot_two_high_hit(
    globs: Seq<GiGlob>,
    registered: Seq<RegisteredGlob>,
    root: Seq<u8>,
    path: Seq<u8>,
    is_dir: bool,
    strip: Seq<u8>,
    hit_wl: bool,
    hit_od: bool,
    miss_actual: Seq<u8>,
    hit_original: Seq<u8>,
    hit_actual: Seq<u8>,
)
    requires
        globs.len() == 2,
        registered.len() == 2,
        registered[0].pattern@ == miss_actual,
        registered[1].pattern@ == hit_actual,
        !registered[0].case_insensitive,
        !registered[1].case_insensitive,
        globs[1].original@ == hit_original,
        globs[1].actual@ == hit_actual,
        globs[1].is_whitelist == hit_wl,
        globs[1].is_only_dir == hit_od,
        globs[1].from matches None,
        (globs[0].is_only_dir ==> is_dir),
        (hit_od ==> is_dir),
        gi_strip_spec(root, path) == strip,
        !glob_pat_matches(miss_actual, false, strip),
        glob_pat_matches(hit_actual, false, strip),
    ensures
        gi_slot_view(globs, registered, root, path, is_dir)
            == Some((hit_wl, IgmOrigSpec::Gi((hit_original, hit_actual,
                hit_wl, hit_od,
                match globs[1].from {
                    Some(p) => Some(p.bytes@),
                    None => None,
                }))))
{
    reveal(gi_slot_view);
    reveal(gi_decide);
    reveal_with_fuel(gi_decide_from, 3);
    gi_decide_from_step(globs, registered, gi_strip_spec(root, path),
        is_dir, 1);
    gi_decide_from_step(globs, registered, gi_strip_spec(root, path),
        is_dir, 0);
    assert(gi_decide_from(globs, registered, gi_strip_spec(root, path),
        is_dir, 1) == Some((hit_wl, 1)));
}

/// A two-line store where the scan FALLS past a masked-out HIGHER
/// index onto the LOWER hit (the matched-decision "idx1 misses, idx0
/// decides" face; e.g. lines "foo\n!bar" against candidate "foo").
proof fn gi_slot_two_fall_hit(
    globs: Seq<GiGlob>,
    registered: Seq<RegisteredGlob>,
    root: Seq<u8>,
    path: Seq<u8>,
    is_dir: bool,
    strip: Seq<u8>,
    hit_wl: bool,
    hit_od: bool,
    hit_original: Seq<u8>,
    hit_actual: Seq<u8>,
    miss_actual: Seq<u8>,
)
    requires
        globs.len() == 2,
        registered.len() == 2,
        registered[0].pattern@ == hit_actual,
        registered[1].pattern@ == miss_actual,
        !registered[0].case_insensitive,
        !registered[1].case_insensitive,
        globs[0].original@ == hit_original,
        globs[0].actual@ == hit_actual,
        globs[0].is_whitelist == hit_wl,
        globs[0].is_only_dir == hit_od,
        globs[0].from matches None,
        (globs[1].is_only_dir ==> is_dir),
        (hit_od ==> is_dir),
        gi_strip_spec(root, path) == strip,
        !glob_pat_matches(miss_actual, false, strip),
        glob_pat_matches(hit_actual, false, strip),
    ensures
        gi_slot_view(globs, registered, root, path, is_dir)
            == Some((hit_wl, IgmOrigSpec::Gi((hit_original, hit_actual,
                hit_wl, hit_od,
                match globs[0].from {
                    Some(p) => Some(p.bytes@),
                    None => None,
                }))))
{
    reveal(gi_slot_view);
    reveal(gi_decide);
    reveal_with_fuel(gi_decide_from, 3);
    gi_decide_from_step(globs, registered, gi_strip_spec(root, path),
        is_dir, 1);
    gi_decide_from_step(globs, registered, gi_strip_spec(root, path),
        is_dir, 0);
    assert(gi_decide_from(globs, registered, gi_strip_spec(root, path),
        is_dir, 1) == Some((hit_wl, 0)));
}

/// A two-line store where BOTH entries miss per the admits.
proof fn gi_slot_two_miss(
    globs: Seq<GiGlob>,
    registered: Seq<RegisteredGlob>,
    root: Seq<u8>,
    path: Seq<u8>,
    is_dir: bool,
    strip: Seq<u8>,
    miss0: Seq<u8>,
    miss1: Seq<u8>,
)
    requires
        globs.len() == 2,
        registered.len() == 2,
        registered[0].pattern@ == miss0,
        registered[1].pattern@ == miss1,
        !registered[0].case_insensitive,
        !registered[1].case_insensitive,
        (globs[0].is_only_dir ==> is_dir),
        (globs[1].is_only_dir ==> is_dir),
        gi_strip_spec(root, path) == strip,
        !glob_pat_matches(miss0, false, strip),
        !glob_pat_matches(miss1, false, strip),
    ensures gi_slot_view(globs, registered, root, path, is_dir) == None
{
    reveal(gi_slot_view);
    reveal(gi_decide);
    reveal_with_fuel(gi_decide_from, 3);
    gi_decide_from_step(globs, registered, gi_strip_spec(root, path),
        is_dir, 1);
    gi_decide_from_step(globs, registered, gi_strip_spec(root, path),
        is_dir, 0);
    assert(gi_decide_from(globs, registered, gi_strip_spec(root, path),
        is_dir, 1) matches None);
}

/// A two-line store where BOTH lines hit the candidate per the
/// admits: the scan starts at the TOP index, so the HIGHER store
/// index (the later-added line) decides (dir.rs's per-file order /
/// DP25 reversed-scan).
proof fn gi_slot_two_top_hit(
    globs: Seq<GiGlob>,
    registered: Seq<RegisteredGlob>,
    root: Seq<u8>,
    path: Seq<u8>,
    is_dir: bool,
    strip: Seq<u8>,
    hit_wl: bool,
    hit_od: bool,
    hit_original: Seq<u8>,
    hit_actual: Seq<u8>,
)
    requires
        globs.len() == 2,
        registered.len() == 2,
        registered[1].pattern@ == hit_actual,
        !registered[1].case_insensitive,
        globs[1].original@ == hit_original,
        globs[1].actual@ == hit_actual,
        globs[1].is_whitelist == hit_wl,
        globs[1].is_only_dir == hit_od,
        globs[1].from matches None,
        (hit_od ==> is_dir),
        gi_strip_spec(root, path) == strip,
        glob_pat_matches(hit_actual, false, strip),
    ensures
        gi_slot_view(globs, registered, root, path, is_dir)
            == Some((hit_wl, IgmOrigSpec::Gi((hit_original, hit_actual,
                hit_wl, hit_od,
                match globs[1].from {
                    Some(p) => Some(p.bytes@),
                    None => None,
                }))))
{
    reveal(gi_slot_view);
    reveal(gi_decide);
    reveal_with_fuel(gi_decide_from, 3);
    gi_decide_from_step(globs, registered, gi_strip_spec(root, path),
        is_dir, 1);
    assert(gi_decide_from(globs, registered, gi_strip_spec(root, path),
        is_dir, 1) == Some((hit_wl, 1)));
}

/// Two equal-length byte seqs equal at every index are equal (the
/// push-chain to literal bridge of the join rows).
proof fn seq_ext_eq(a: Seq<u8>, b: Seq<u8>)
    requires
        a.len() == b.len(),
        forall|i: int| #![trigger a[i]] 0 <= i < a.len()
            ==> a[i] == b[i],
    ensures a == b
{
}


/// The concrete strip drills: ONE proven body per (root-length,
/// tail-length) shape, scalar-parameterized so every link stays
/// ground at the call site. The subject path always spells
/// root ++ "/" ++ tail (the root carries the store's root path and
/// the joined absolute base restores the rest): gi_strip_spec's
/// chain (gitignore.rs:1751-1767 -- peel "./", strip the root,
/// strip the leading "/") evaluates here once; the tail's first
/// byte must not be a slash so the inner strip is a real strip.
proof fn gstrip_p3t7(
    r0: u8, r1: u8, r2: u8,
    t0: u8, t1: u8, t2: u8, t3: u8, t4: u8, t5: u8, t6: u8,
    path: Seq<u8>,
)
    requires
        r0 == 0x2F,
        t0 != 0x2F,
        path.len() == 3 + 1 + 7,
        path[0] == r0 && path[1] == r1 && path[2] == r2,
        path[3] == 0x2F,
        path[4] == t0 && path[5] == t1 && path[6] == t2,
        path[7] == t3 && path[8] == t4 && path[9] == t5,
        path[10] == t6,
    ensures
        strip_prefix_spec(seq![r0, r1, r2], path)
            == Some(path.subrange(3, path.len() as int)),
        gi_strip_spec(seq![r0, r1, r2], path)
            == seq![t0, t1, t2, t3, t4, t5, t6],
{
    let prefix = seq![r0, r1, r2];
    let after = path.subrange(3, path.len() as int);
    let tail = seq![t0, t1, t2, t3, t4, t5, t6];
    assert(prefix[0] == path[0]);
    assert(prefix[1] == path[1]);
    assert(prefix[2] == path[2]);
    assert(bytes_prefix_eq(prefix, path));
    assert(after.len() == 1 + 7);
    assert(after[0] == path[3]);
    assert(after[1] == path[4]);
    assert(after[2] == path[5]);
    assert(after[3] == path[6]);
    assert(after[4] == path[7]);
    assert(after[5] == path[8]);
    assert(after[6] == path[9]);
    assert(after[7] == path[10]);
    assert(after[0] == 0x2F);
    assert(after.subrange(1, after.len() as int).len() == 7);
    assert(after.subrange(1, after.len() as int)[0] == t0);
    assert(after.subrange(1, after.len() as int)[1] == t1);
    assert(after.subrange(1, after.len() as int)[2] == t2);
    assert(after.subrange(1, after.len() as int)[3] == t3);
    assert(after.subrange(1, after.len() as int)[4] == t4);
    assert(after.subrange(1, after.len() as int)[5] == t5);
    assert(after.subrange(1, after.len() as int)[6] == t6);
    assert(after.subrange(1, after.len() as int) == tail);
    assert(strip_prefix_spec(seq![0x2F], after) == Some(tail));
    assert(strip_prefix_spec(prefix, path) == Some(after));
    assert(!bytes_prefix_eq(seq![0x2E, 0x2F], path));
    assert(!is_file_name_spec(path));
    assert(gi_strip_spec(prefix, path) == tail);
}

/// The no-strip rung of the bare root: "/" against a one-byte name
/// that differs at the first byte (the strip_keep None arm; the
/// #IG-19 scalar-helper recipe over the negative prefix row).
proof fn strip_keep_nostrip(nm: Seq<u8>)
    requires
        nm.len() == 0 || nm[0] != 0x2F,
    ensures strip_keep(seq![0x2Fu8], nm) == nm,
{
    assert(seq![0x2Fu8].len() == 1);
    assert(!bytes_prefix_eq(seq![0x2Fu8], nm));
    assert(strip_prefix_spec(seq![0x2Fu8], nm) matches None);
}

/// The (3,4) shape: the ".hid" tail of the consult row.
proof fn gstrip_p3t4(
    r0: u8, r1: u8, r2: u8,
    t0: u8, t1: u8, t2: u8, t3: u8,
    path: Seq<u8>,
)
    requires
        r0 == 0x2F,
        t0 != 0x2F,
        path.len() == 3 + 1 + 4,
        path[0] == r0 && path[1] == r1 && path[2] == r2,
        path[3] == 0x2F,
        path[4] == t0 && path[5] == t1 && path[6] == t2,
        path[7] == t3,
    ensures
        strip_prefix_spec(seq![r0, r1, r2], path)
            == Some(path.subrange(3, path.len() as int)),
        gi_strip_spec(seq![r0, r1, r2], path)
            == seq![t0, t1, t2, t3],
{
    let prefix = seq![r0, r1, r2];
    let after = path.subrange(3, path.len() as int);
    let tail = seq![t0, t1, t2, t3];
    assert(prefix[0] == path[0]);
    assert(prefix[1] == path[1]);
    assert(prefix[2] == path[2]);
    assert(bytes_prefix_eq(prefix, path));
    assert(after.len() == 1 + 4);
    assert(after[0] == path[3]);
    assert(after[1] == path[4]);
    assert(after[2] == path[5]);
    assert(after[3] == path[6]);
    assert(after[4] == path[7]);
    assert(after[0] == 0x2F);
    assert(after.subrange(1, after.len() as int).len() == 4);
    assert(after.subrange(1, after.len() as int)[0] == t0);
    assert(after.subrange(1, after.len() as int)[1] == t1);
    assert(after.subrange(1, after.len() as int)[2] == t2);
    assert(after.subrange(1, after.len() as int)[3] == t3);
    assert(after.subrange(1, after.len() as int) == tail);
    assert(strip_prefix_spec(seq![0x2F], after) == Some(tail));
    assert(strip_prefix_spec(prefix, path) == Some(after));
    assert(!bytes_prefix_eq(seq![0x2E, 0x2F], path));
    assert(!is_file_name_spec(path));
    assert(gi_strip_spec(prefix, path) == tail);
}

/// The (3,5) shape: the "sub/x" tail of the multi-root rows.
proof fn gstrip_p3t5(
    r0: u8, r1: u8, r2: u8,
    t0: u8, t1: u8, t2: u8, t3: u8, t4: u8,
    path: Seq<u8>,
)
    requires
        r0 == 0x2F,
        t0 != 0x2F,
        path.len() == 3 + 1 + 5,
        path[0] == r0 && path[1] == r1 && path[2] == r2,
        path[3] == 0x2F,
        path[4] == t0 && path[5] == t1 && path[6] == t2,
        path[7] == t3 && path[8] == t4,
    ensures
        strip_prefix_spec(seq![r0, r1, r2], path)
            == Some(path.subrange(3, path.len() as int)),
        gi_strip_spec(seq![r0, r1, r2], path)
            == seq![t0, t1, t2, t3, t4],
{
    let prefix = seq![r0, r1, r2];
    let after = path.subrange(3, path.len() as int);
    let tail = seq![t0, t1, t2, t3, t4];
    assert(prefix[0] == path[0]);
    assert(prefix[1] == path[1]);
    assert(prefix[2] == path[2]);
    assert(bytes_prefix_eq(prefix, path));
    assert(after.len() == 1 + 5);
    assert(after[0] == path[3]);
    assert(after[1] == path[4]);
    assert(after[2] == path[5]);
    assert(after[3] == path[6]);
    assert(after[4] == path[7]);
    assert(after[5] == path[8]);
    assert(after[0] == 0x2F);
    assert(after.subrange(1, after.len() as int).len() == 5);
    assert(after.subrange(1, after.len() as int)[0] == t0);
    assert(after.subrange(1, after.len() as int)[1] == t1);
    assert(after.subrange(1, after.len() as int)[2] == t2);
    assert(after.subrange(1, after.len() as int)[3] == t3);
    assert(after.subrange(1, after.len() as int)[4] == t4);
    assert(after.subrange(1, after.len() as int) == tail);
    assert(strip_prefix_spec(seq![0x2F], after) == Some(tail));
    assert(strip_prefix_spec(prefix, path) == Some(after));
    assert(!bytes_prefix_eq(seq![0x2E, 0x2F], path));
    assert(!is_file_name_spec(path));
    assert(gi_strip_spec(prefix, path) == tail);
}

/// The (3,9) shape: the nine-byte tails of the multi-root and
/// rules rows ("foo/x.log", "x/y/x.log").
proof fn gstrip_p3t9(
    r0: u8, r1: u8, r2: u8,
    t0: u8, t1: u8, t2: u8, t3: u8, t4: u8, t5: u8, t6: u8,
    t7: u8, t8: u8,
    path: Seq<u8>,
)
    requires
        r0 == 0x2F,
        t0 != 0x2F,
        path.len() == 3 + 1 + 9,
        path[0] == r0 && path[1] == r1 && path[2] == r2,
        path[3] == 0x2F,
        path[4] == t0 && path[5] == t1 && path[6] == t2,
        path[7] == t3 && path[8] == t4 && path[9] == t5,
        path[10] == t6 && path[11] == t7 && path[12] == t8,
    ensures
        strip_prefix_spec(seq![r0, r1, r2], path)
            == Some(path.subrange(3, path.len() as int)),
        gi_strip_spec(seq![r0, r1, r2], path)
            == seq![t0, t1, t2, t3, t4, t5, t6, t7, t8],
{
    let prefix = seq![r0, r1, r2];
    let after = path.subrange(3, path.len() as int);
    let tail = seq![t0, t1, t2, t3, t4, t5, t6, t7, t8];
    assert(prefix[0] == path[0]);
    assert(prefix[1] == path[1]);
    assert(prefix[2] == path[2]);
    assert(bytes_prefix_eq(prefix, path));
    assert(after.len() == 1 + 9);
    assert(after[0] == path[3]);
    assert(after[1] == path[4]);
    assert(after[2] == path[5]);
    assert(after[3] == path[6]);
    assert(after[4] == path[7]);
    assert(after[5] == path[8]);
    assert(after[6] == path[9]);
    assert(after[7] == path[10]);
    assert(after[8] == path[11]);
    assert(after[9] == path[12]);
    assert(after[0] == 0x2F);
    assert(after.subrange(1, after.len() as int).len() == 9);
    assert(after.subrange(1, after.len() as int)[0] == t0);
    assert(after.subrange(1, after.len() as int)[1] == t1);
    assert(after.subrange(1, after.len() as int)[2] == t2);
    assert(after.subrange(1, after.len() as int)[3] == t3);
    assert(after.subrange(1, after.len() as int)[4] == t4);
    assert(after.subrange(1, after.len() as int)[5] == t5);
    assert(after.subrange(1, after.len() as int)[6] == t6);
    assert(after.subrange(1, after.len() as int)[7] == t7);
    assert(after.subrange(1, after.len() as int)[8] == t8);
    assert(after.subrange(1, after.len() as int) == tail);
    assert(strip_prefix_spec(seq![0x2F], after) == Some(tail));
    assert(strip_prefix_spec(prefix, path) == Some(after));
    assert(!bytes_prefix_eq(seq![0x2E, 0x2F], path));
    assert(!is_file_name_spec(path));
    assert(gi_strip_spec(prefix, path) == tail);
}

/// The (5,3) shape: the repository row's "/td/x"-rooted strips.
proof fn gstrip_p5t3(
    r0: u8, r1: u8, r2: u8, r3: u8, r4: u8,
    t0: u8, t1: u8, t2: u8,
    path: Seq<u8>,
)
    requires
        r0 == 0x2F,
        t0 != 0x2F,
        path.len() == 5 + 1 + 3,
        path[0] == r0 && path[1] == r1 && path[2] == r2,
        path[3] == r3 && path[4] == r4,
        path[5] == 0x2F,
        path[6] == t0 && path[7] == t1 && path[8] == t2,
    ensures
        strip_prefix_spec(seq![r0, r1, r2, r3, r4], path)
            == Some(path.subrange(5, path.len() as int)),
        gi_strip_spec(seq![r0, r1, r2, r3, r4], path)
            == seq![t0, t1, t2],
{
    let prefix = seq![r0, r1, r2, r3, r4];
    let after = path.subrange(5, path.len() as int);
    let tail = seq![t0, t1, t2];
    assert(prefix[0] == path[0]);
    assert(prefix[1] == path[1]);
    assert(prefix[2] == path[2]);
    assert(prefix[3] == path[3]);
    assert(prefix[4] == path[4]);
    assert(bytes_prefix_eq(prefix, path));
    assert(after.len() == 1 + 3);
    assert(after[0] == path[5]);
    assert(after[1] == path[6]);
    assert(after[2] == path[7]);
    assert(after[3] == path[8]);
    assert(after[0] == 0x2F);
    assert(after.subrange(1, after.len() as int).len() == 3);
    assert(after.subrange(1, after.len() as int)[0] == t0);
    assert(after.subrange(1, after.len() as int)[1] == t1);
    assert(after.subrange(1, after.len() as int)[2] == t2);
    assert(after.subrange(1, after.len() as int) == tail);
    assert(strip_prefix_spec(seq![0x2F], after) == Some(tail));
    assert(strip_prefix_spec(prefix, path) == Some(after));
    assert(!bytes_prefix_eq(seq![0x2E, 0x2F], path));
    assert(!is_file_name_spec(path));
    assert(gi_strip_spec(prefix, path) == tail);
}

// =========================================================================
// UT-P: the precedence pairs (upstream dir.rs tests 1176-1344)
// =========================================================================

/// explicit_ignore (dir.rs:1176-1188): the ADDED ignore outranks the
/// directory pools; foo ignored (the "**/foo" line decides below the
/// masked-out "!bar" line), bar whitelisted (the LATER "!bar" line is
/// the higher store index), baz unmatched. INLINE stack construction
/// (#IG-19 prescription: no layered quantified constructor posts;
/// every field path traces to a constructor component).
fn row_explicit_ignore() -> (r: bool)
    ensures r
{
    // the driver's EXPLICIT column: one matcher, two stores, empty
    // matcher root (Gitignore::new's cwd), lines "foo\n!bar"
    let m_foo = h_matcher2(Vec::new(), b_ss_foo(), false, false,
        b_ss_bar(), true, false);
    let mut expl: Vec<Gitignore> = Vec::new();
    expl.push(m_foo);
    // the head: dir "td", empty pools
    let head_e_custom = h_empty();
    let head_e_ignore = h_empty();
    let head_e_gi = h_empty();
    let head_e_excl = h_empty();
    let head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: head_e_custom,
        ignore_matcher: head_e_ignore,
        git_ignore_matcher: head_e_gi,
        git_exclude_matcher: head_e_excl,
    };
    // the builder-root tail
    let rootnd_e_custom = h_empty();
    let rootnd_e_ignore = h_empty();
    let rootnd_e_gi = h_empty();
    let rootnd_e_excl = h_empty();
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: rootnd_e_custom,
        ignore_matcher: rootnd_e_ignore,
        git_ignore_matcher: rootnd_e_gi,
        git_exclude_matcher: rootnd_e_excl,
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: expl,
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: None };
    assert(ig_wf(&ig));

    // the mask admits (driver MASK rows: (actual, candidate) pairs;
    // S14 columns line"foo"/line"bar"/line"!bar" quote each)
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x66, 0x6F, 0x6F]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x66, 0x6F, 0x6F]) == true);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x62, 0x61, 0x72]) == true);

    proof {
        // the move equalities: every field path traces to its
        // constructor component (no quantified transfer)
        assert(ig.inner.explicit_ignores@ == seq![m_foo]);
        assert(ig.nodes@ == seq![head, rootnd]);
        assert(ig.nodes@[0] == head);
        assert(ig.nodes@[1] == rootnd);
        // rung 0: the shape / gates
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(first_abs, 4);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 3);
        reveal(iglib::pathutil::is_file_name_spec);
        assert(ig.nodes@.len() == 2);
        assert(!ig.nodes@[0].is_absolute_parent);
        assert(ig.nodes@[1].is_absolute_parent);
        assert(first_abs(ig.nodes@, 0) == 1);
        assert(ig.inner.opts.require_git == true);
        assert(any_has_git(ig.nodes@, 0) == false);
        assert(ig_any_git(&ig) == false);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        // rung 1: the head's four empty slots
        assert(head.custom_ignore_matcher == head_e_custom);
        assert(head.ignore_matcher == head_e_ignore);
        assert(head.git_ignore_matcher == head_e_gi);
        assert(head.git_exclude_matcher == head_e_excl);
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x66, 0x6F, 0x6F], false, false) == mi_st_none());
        // rung 2: no after-barrier scan (absolute_base None)
        assert(ig.absolute_base@ matches None);
        // rung 3: the global store is empty
        assert(ig.inner.git_global_matcher == gg_e);
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        // rung 4: the explicit store: strip leaves "foo" bare
        reveal(iglib::gitignore::gi_strip_spec);
        assert(ig.inner.explicit_ignores@[0] == m_foo);
        assert(gi_strip_spec(
            ig.inner.explicit_ignores@[0].root.bytes@,
            seq![0x66, 0x6F, 0x6F]) == seq![0x66, 0x6F, 0x6F]);
        gi_slot_two_fall_hit(
            ig.inner.explicit_ignores@[0].globs@,
            ig.inner.explicit_ignores@[0].set.registered@,
            ig.inner.explicit_ignores@[0].root.bytes@,
            seq![0x66, 0x6F, 0x6F],
            false,
            seq![0x66, 0x6F, 0x6F],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        assert(mi_explicit(ig.inner.explicit_ignores@, 0,
            seq![0x66, 0x6F, 0x6F], false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
        // rung 5: the cascade singleton
        assert(dir_mi_spec(&ig, seq![0x66, 0x6F, 0x6F], false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
    }

    // candidate "foo"
    let m1 = ig.matched(b_foo().as_slice(), false);
    assert(ig_m_view(&m1)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], false, false, None)))));
    assert(m1 matches Match::Ignore(_));

    // candidate "bar": the LATER line ("!bar") is the hit in the store
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x62, 0x61, 0x72]) == false);
    proof {
        reveal_with_fuel(mi_explicit, 3);
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x62, 0x61, 0x72], false, false) == mi_st_none());
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        assert(gi_strip_spec(
            ig.inner.explicit_ignores@[0].root.bytes@,
            seq![0x62, 0x61, 0x72]) == seq![0x62, 0x61, 0x72]);
        gi_slot_two_high_hit(
            ig.inner.explicit_ignores@[0].globs@,
            ig.inner.explicit_ignores@[0].set.registered@,
            ig.inner.explicit_ignores@[0].root.bytes@,
            seq![0x62, 0x61, 0x72],
            false,
            seq![0x62, 0x61, 0x72],
            true,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        assert(dir_mi_spec(&ig, seq![0x62, 0x61, 0x72], false)
            == Some((true, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8],
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                true, false, None)))));
    }
    let m2 = ig.matched(b_bar().as_slice(), false);
    assert(ig_m_view(&m2)
        == Some((true, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], true, false, None)))));
    assert(m2 matches Match::Whitelist(_));

    // candidate "baz": both store lines miss
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x62, 0x61, 0x7A]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x62, 0x61, 0x7A]) == false);
    proof {
        reveal_with_fuel(mi_explicit, 3);
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false);
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false);
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x62, 0x61, 0x7A], false, false) == mi_st_none());
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false);
        assert(gi_strip_spec(
            ig.inner.explicit_ignores@[0].root.bytes@,
            seq![0x62, 0x61, 0x7A]) == seq![0x62, 0x61, 0x7A]);
        gi_slot_two_miss(
            ig.inner.explicit_ignores@[0].globs@,
            ig.inner.explicit_ignores@[0].set.registered@,
            ig.inner.explicit_ignores@[0].root.bytes@,
            seq![0x62, 0x61, 0x7A],
            false,
            seq![0x62, 0x61, 0x7A],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        assert(dir_mi_spec(&ig, seq![0x62, 0x61, 0x7A], false) == None);
    }
    let m3 = ig.matched(b_baz().as_slice(), false);
    assert(ig_m_view(&m3) == None);
    assert(m3 matches Match::None);
    true
}

/// ignore (dir.rs:1257-1266): the .ignore pool applies without any
/// git (m_ignore is not any_git-gated); lines "foo\n!bar" -> foo
/// ignored, bar whitelisted, baz unmatched.
fn row_ignore() -> (r: bool)
    ensures r
{
    let ig_m = h_matcher2(b_td_root(), b_ss_foo(), false, false,
        b_ss_bar(), true, false);
    let head_e_custom = h_empty();
    let head_e_gi = h_empty();
    let head_e_excl = h_empty();
    let head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: head_e_custom,
        ignore_matcher: ig_m,
        git_ignore_matcher: head_e_gi,
        git_exclude_matcher: head_e_excl,
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: None };
    assert(ig_wf(&ig));

    // the mask admits (S14 columns line"foo" / line"!bar" / line"bar")
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x66, 0x6F, 0x6F]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x66, 0x6F, 0x6F]) == true);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x62, 0x61, 0x72]) == true);

    proof {
        assert(ig.nodes@ == seq![head, rootnd]);
        assert(ig.nodes@[0] == head);
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(first_abs, 4);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 3);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        assert(ig.nodes@.len() == 2);
        assert(first_abs(ig.nodes@, 0) == 1);
        assert(ig.inner.opts.require_git == true);
        assert(any_has_git(ig.nodes@, 0) == false);
        assert(ig_any_git(&ig) == false);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        // the head's three empty slots
        assert(head.custom_ignore_matcher == head_e_custom);
        assert(head.git_ignore_matcher == head_e_gi);
        assert(head.git_exclude_matcher == head_e_excl);
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        // the .ignore store: strip leaves "foo" bare
        assert(gi_strip_spec(
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F]) == seq![0x66, 0x6F, 0x6F]);
        gi_slot_two_fall_hit(
            ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F],
            false,
            seq![0x66, 0x6F, 0x6F],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x66, 0x6F, 0x6F], false, false)
            == MiScanSt {
                m_custom: None,
                m_ignore: Some((false, IgmOrigSpec::Gi((
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    false, false, None)))),
                m_gi: None,
                m_gi_exclude: None,
                saw_git: false,
            });
        // no after-barrier scan; the global gate is closed (any_git
        // false); the explicit pool is empty
        assert(ig.absolute_base@ matches None);
        assert(ig.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            seq![0x66, 0x6F, 0x6F], false) == None);
        assert(dir_mi_spec(&ig, seq![0x66, 0x6F, 0x6F], false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
    }
    let m1 = ig.matched(b_foo().as_slice(), false);
    assert(ig_m_view(&m1)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], false, false, None)))));
    assert(m1 matches Match::Ignore(_));

    // candidate "bar": the LATER "!bar" line is the hit
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x62, 0x61, 0x72]) == false);
    proof {
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        assert(gi_strip_spec(
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72]) == seq![0x62, 0x61, 0x72]);
        gi_slot_two_high_hit(
            ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72],
            false,
            seq![0x62, 0x61, 0x72],
            true,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x62, 0x61, 0x72], false, false)
            == MiScanSt {
                m_custom: None,
                m_ignore: Some((true, IgmOrigSpec::Gi((
                    seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                    seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                    true, false, None)))),
                m_gi: None,
                m_gi_exclude: None,
                saw_git: false,
            });
        assert(dir_mi_spec(&ig, seq![0x62, 0x61, 0x72], false)
            == Some((true, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8],
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                true, false, None)))));
    }
    let m2 = ig.matched(b_bar().as_slice(), false);
    assert(ig_m_view(&m2)
        == Some((true, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], true, false, None)))));
    assert(m2 matches Match::Whitelist(_));

    // candidate "baz": both lines miss
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x62, 0x61, 0x7A]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x62, 0x61, 0x7A]) == false);
    proof {
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false);
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false);
        assert(gi_strip_spec(
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A]) == seq![0x62, 0x61, 0x7A]);
        gi_slot_two_miss(
            ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A],
            false,
            seq![0x62, 0x61, 0x7A],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        assert(dir_mi_spec(&ig, seq![0x62, 0x61, 0x7A], false) == None);
    }
    let m3 = ig.matched(b_baz().as_slice(), false);
    assert(ig_m_view(&m3) == None);
    assert(m3 matches Match::None);
    true
}

/// gitignore_no_git (dir.rs:1229-1239): require_git on and no .git
/// anywhere -> any_git false -> the git pools stay closed: three
/// verdicts None (no mask admit: the store is never consulted).
fn row_gitignore_no_git() -> (r: bool)
    ensures r
{
    let gi_m = h_matcher2(b_td_root(), b_ss_foo(), false, false,
        b_ss_bar(), true, false);
    let head_e_custom = h_empty();
    let head_e_ignore = h_empty();
    let head_e_excl = h_empty();
    let head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: head_e_custom,
        ignore_matcher: head_e_ignore,
        git_ignore_matcher: gi_m,
        git_exclude_matcher: head_e_excl,
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: None };
    assert(ig_wf(&ig));

    proof {
        assert(ig.nodes@ == seq![head, rootnd]);
        assert(ig.nodes@[0] == head);
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(first_abs, 4);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 3);
        reveal(iglib::pathutil::is_file_name_spec);
        assert(ig.nodes@.len() == 2);
        assert(first_abs(ig.nodes@, 0) == 1);
        assert(ig.inner.opts.require_git == true);
        assert(any_has_git(ig.nodes@, 0) == false);
        assert(ig_any_git(&ig) == false);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        assert(ig.absolute_base@ matches None);
        assert(ig.inner.explicit_ignores@.len() == 0);
        // the head step: empty custom/ignore/exclude slots and the
        // CLOSED gi gates leave the state empty, for every candidate
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x66, 0x6F, 0x6F], false, false) == mi_st_none());
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x62, 0x61, 0x72], false, false) == mi_st_none());
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x62, 0x61, 0x7A], false, false) == mi_st_none());
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            seq![0x66, 0x6F, 0x6F], false) == None);
        assert(dir_mi_spec(&ig, seq![0x66, 0x6F, 0x6F], false) == None);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            seq![0x62, 0x61, 0x72], false) == None);
        assert(dir_mi_spec(&ig, seq![0x62, 0x61, 0x72], false) == None);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            seq![0x62, 0x61, 0x7A], false) == None);
        assert(dir_mi_spec(&ig, seq![0x62, 0x61, 0x7A], false) == None);
    }
    let m1 = ig.matched(b_foo().as_slice(), false);
    assert(ig_m_view(&m1) == None);
    assert(m1 matches Match::None);
    let m2 = ig.matched(b_bar().as_slice(), false);
    assert(ig_m_view(&m2) == None);
    assert(m2 matches Match::None);
    let m3 = ig.matched(b_baz().as_slice(), false);
    assert(ig_m_view(&m3) == None);
    assert(m3 matches Match::None);
    true
}

/// gitignore_allowed_no_git (dir.rs:1241-1254): require_git OFF ->
/// any_git true by constitution (dir.rs:590) -> the gi pool is live:
/// foo ignored, bar whitelisted, baz unmatched.
fn row_gitignore_allowed_no_git() -> (r: bool)
    ensures r
{
    let gi_m = h_matcher2(b_td_root(), b_ss_foo(), false, false,
        b_ss_bar(), true, false);
    let head_e_custom = h_empty();
    let head_e_ignore = h_empty();
    let head_e_excl = h_empty();
    let head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: head_e_custom,
        ignore_matcher: head_e_ignore,
        git_ignore_matcher: gi_m,
        git_exclude_matcher: head_e_excl,
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_no_require_git();
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: None };
    assert(ig_wf(&ig));

    // the mask admits (S14 columns line"foo" / line"bar" / line"!bar")
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x66, 0x6F, 0x6F]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x66, 0x6F, 0x6F]) == true);

    proof {
        assert(ig.nodes@ == seq![head, rootnd]);
        assert(ig.nodes@[0] == head);
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(first_abs, 4);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 3);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        assert(ig.nodes@.len() == 2);
        assert(first_abs(ig.nodes@, 0) == 1);
        assert(ig.inner.opts.require_git == false);
        assert(ig_any_git(&ig) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        // the head's three empty slots
        assert(head.custom_ignore_matcher == head_e_custom);
        assert(head.ignore_matcher == head_e_ignore);
        assert(head.git_exclude_matcher == head_e_excl);
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        // the gi store: strip leaves "foo" bare
        assert(gi_strip_spec(
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F]) == seq![0x66, 0x6F, 0x6F]);
        gi_slot_two_fall_hit(
            ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F],
            false,
            seq![0x66, 0x6F, 0x6F],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x66, 0x6F, 0x6F], false, true)
            == MiScanSt {
                m_custom: None,
                m_ignore: None,
                m_gi: Some((false, IgmOrigSpec::Gi((
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    false, false, None)))),
                m_gi_exclude: None,
                saw_git: false,
            });
        // the global store is empty but LIVE (any_git true)
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        assert(ig.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            seq![0x66, 0x6F, 0x6F], false) == None);
        assert(dir_mi_spec(&ig, seq![0x66, 0x6F, 0x6F], false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
    }
    let m1 = ig.matched(b_foo().as_slice(), false);
    assert(ig_m_view(&m1)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], false, false, None)))));
    assert(m1 matches Match::Ignore(_));

    // candidate "bar": the LATER "!bar" line is the hit
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x62, 0x61, 0x72]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x62, 0x61, 0x72]) == true);
    proof {
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        assert(gi_strip_spec(
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72]) == seq![0x62, 0x61, 0x72]);
        gi_slot_two_high_hit(
            ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72],
            false,
            seq![0x62, 0x61, 0x72],
            true,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            seq![0x62, 0x61, 0x72], false) == None);
        assert(dir_mi_spec(&ig, seq![0x62, 0x61, 0x72], false)
            == Some((true, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8],
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                true, false, None)))));
    }
    let m2 = ig.matched(b_bar().as_slice(), false);
    assert(ig_m_view(&m2)
        == Some((true, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], true, false, None)))));
    assert(m2 matches Match::Whitelist(_));

    // candidate "baz": both lines miss
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x62, 0x61, 0x7A]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x62, 0x61, 0x7A]) == false);
    proof {
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false);
        assert(gi_strip_spec(
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A]) == seq![0x62, 0x61, 0x7A]);
        gi_slot_two_miss(
            ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A],
            false,
            seq![0x62, 0x61, 0x7A],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            seq![0x62, 0x61, 0x7A], false) == None);
        assert(dir_mi_spec(&ig, seq![0x62, 0x61, 0x7A], false) == None);
    }
    let m3 = ig.matched(b_baz().as_slice(), false);
    assert(ig_m_view(&m3) == None);
    assert(m3 matches Match::None);
    true
}

/// custom_ignore_over_ignore (dir.rs:1284-1298): the custom pool
/// outranks the .ignore pool -- "!foo" custom + "foo" .ignore ->
/// whitelisted, with the ORIGIN in the custom slot (the Gi view of
/// the custom store's whitelist entry).
fn row_custom_over_ignore() -> (r: bool)
    ensures r
{
    let custom_m = h_matcher1(b_td_root(), b_ss_foo(), true, false);
    let ig_m = h_matcher1(b_td_root(), b_ss_foo(), false, false);
    let head_e_gi = h_empty();
    let head_e_excl = h_empty();
    let head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: custom_m,
        ignore_matcher: ig_m,
        git_ignore_matcher: head_e_gi,
        git_exclude_matcher: head_e_excl,
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let mut custom_names: Vec<Vec<u8>> = Vec::new();
    custom_names.push(b_xcustom());
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: custom_names,
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: None };
    assert(ig_wf(&ig));

    // the mask admit (S14 column line"!foo": foo=1): both pools'
    // "**/foo" actuals hit the candidate
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x66, 0x6F, 0x6F]) == true);

    proof {
        assert(ig.nodes@ == seq![head, rootnd]);
        assert(ig.nodes@[0] == head);
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(first_abs, 4);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 3);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        assert(ig.nodes@.len() == 2);
        assert(first_abs(ig.nodes@, 0) == 1);
        assert(ig.inner.opts.require_git == true);
        assert(any_has_git(ig.nodes@, 0) == false);
        assert(ig_any_git(&ig) == false);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        // the head's two empty slots
        assert(head.git_ignore_matcher == head_e_gi);
        assert(head.git_exclude_matcher == head_e_excl);
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        // both live pools hit; strip leaves "foo" bare in each
        assert(gi_strip_spec(
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F]) == seq![0x66, 0x6F, 0x6F]);
        assert(gi_strip_spec(
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F]) == seq![0x66, 0x6F, 0x6F]);
        gi_slot_one_eval(
            ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F],
            false,
            seq![0x66, 0x6F, 0x6F],
            true,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        gi_slot_one_eval(
            ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F],
            false,
            seq![0x66, 0x6F, 0x6F],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x66, 0x6F, 0x6F], false, false)
            == MiScanSt {
                m_custom: Some((true, IgmOrigSpec::Gi((
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    true, false, None)))),
                m_ignore: Some((false, IgmOrigSpec::Gi((
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    false, false, None)))),
                m_gi: None,
                m_gi_exclude: None,
                saw_git: false,
            });
        assert(ig.absolute_base@ matches None);
        assert(ig.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            seq![0x66, 0x6F, 0x6F], false) == None);
        // the cascade: custom outranks .ignore
        assert(dir_mi_spec(&ig, seq![0x66, 0x6F, 0x6F], false)
            == Some((true, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                true, false, None)))));
    }
    let m = ig.matched(b_foo().as_slice(), false);
    assert(ig_m_view(&m)
        == Some((true, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], true, false, None)))));
    assert(m matches Match::Whitelist(_));
    true
}

/// ignore_over_gitignore (dir.rs:1318-1328): "!foo" at .ignore
/// beats "foo" at .gitignore -- and without any .git the gi pool is
/// gated closed (any_git false), so its store is never consulted.
fn row_ignore_over_gitignore() -> (r: bool)
    ensures r
{
    let ig_m = h_matcher1(b_td_root(), b_ss_foo(), true, false);
    let gi_m = h_matcher1(b_td_root(), b_ss_foo(), false, false);
    let head_e_custom = h_empty();
    let head_e_excl = h_empty();
    let head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: head_e_custom,
        ignore_matcher: ig_m,
        git_ignore_matcher: gi_m,
        git_exclude_matcher: head_e_excl,
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: None };
    assert(ig_wf(&ig));

    // the mask admit (S14 column line"!foo": foo=1): the .ignore
    // store's "**/foo" actual hits the candidate
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x66, 0x6F, 0x6F]) == true);

    proof {
        assert(ig.nodes@ == seq![head, rootnd]);
        assert(ig.nodes@[0] == head);
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(first_abs, 4);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 3);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        assert(ig.nodes@.len() == 2);
        assert(first_abs(ig.nodes@, 0) == 1);
        assert(ig.inner.opts.require_git == true);
        assert(any_has_git(ig.nodes@, 0) == false);
        assert(ig_any_git(&ig) == false);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        // the head's empty custom/exclude slots
        assert(head.custom_ignore_matcher == head_e_custom);
        assert(head.git_exclude_matcher == head_e_excl);
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        // the .ignore store hits; the gi store stays gated CLOSED
        assert(gi_strip_spec(
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F]) == seq![0x66, 0x6F, 0x6F]);
        gi_slot_one_eval(
            ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F],
            false,
            seq![0x66, 0x6F, 0x6F],
            true,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x66, 0x6F, 0x6F], false, false)
            == MiScanSt {
                m_custom: None,
                m_ignore: Some((true, IgmOrigSpec::Gi((
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    true, false, None)))),
                m_gi: None,
                m_gi_exclude: None,
                saw_git: false,
            });
        assert(ig.absolute_base@ matches None);
        assert(ig.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            seq![0x66, 0x6F, 0x6F], false) == None);
        // the cascade: .ignore outranks .gitignore
        assert(dir_mi_spec(&ig, seq![0x66, 0x6F, 0x6F], false)
            == Some((true, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                true, false, None)))));
    }
    let m = ig.matched(b_foo().as_slice(), false);
    assert(ig_m_view(&m)
        == Some((true, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], true, false, None)))));
    assert(m matches Match::Whitelist(_));
    true
}
// =========================================================================
// UT-B / UT-A: the barrier, the exclude pool and the absolute-parent
// families (upstream dir.rs tests 1190, 1331, 1395, 1418)
// =========================================================================

/// exclude_lowest (dir.rs:1332-1344): the .git/info/exclude pool
/// loses to both .ignore and .gitignore whitelists ("!foo" at
/// .gitignore, "!bar" at .ignore) but still decides when nothing
/// above matched (candidate baz below; the exclude store re-spelled
/// to two lines "bar\nbaz" carrying the same three-way geometry --
/// upstream writes "foo\nbar\nbaz" and names it "the lowest
/// precedent" pool). INLINE construction per #IG-19.
fn row_exclude_lowest() -> (r: bool)
    ensures r
{
    // ".gitignore" line "!foo"; ".ignore" line "!bar"
    let gi_m = h_matcher1(b_td_root(), b_ss_foo(), true, false);
    let ig_m = h_matcher1(b_td_root(), b_ss_bar(), true, false);
    // ".git/info/exclude" lines "bar\nbaz" (re-spelled)
    let excl_m = h_matcher2(b_td_root(), b_ss_bar(), false, false,
        b_ss_baz(), false, false);
    let head_e_custom = h_empty();
    let head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: head_e_custom,
        ignore_matcher: ig_m,
        git_ignore_matcher: gi_m,
        git_exclude_matcher: excl_m,
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: None };
    assert(ig_wf(&ig));

    // the mask admits (S14 columns line"foo" / line"bar" / line"baz"
    // / line"!foo" / line"!bar": the two-line exclude store quotes
    // both the bar and baz columns)
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x66, 0x6F, 0x6F]) == true);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x62, 0x61, 0x72]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x62, 0x61, 0x7A]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x66, 0x6F, 0x6F]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x62, 0x61, 0x72]) == true);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x62, 0x61, 0x7A]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x7A], false, seq![0x66, 0x6F, 0x6F]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x7A], false, seq![0x62, 0x61, 0x72]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x7A], false, seq![0x62, 0x61, 0x7A]) == true);

    // candidate "foo": whitelisted by the .gitignore "!foo" line
    proof {
        assert(ig.nodes@ == seq![head, rootnd]);
        assert(ig.nodes@[0] == head);
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(first_abs, 4);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 3);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        assert(ig.nodes@.len() == 2);
        assert(first_abs(ig.nodes@, 0) == 1);
        assert(ig.inner.opts.require_git == true);
        assert(any_has_git(ig.nodes@, 0) == true);
        assert(ig_any_git(&ig) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        assert(head.custom_ignore_matcher == head_e_custom);
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        // the ".ignore" line "!bar" misses "foo"
        assert(gi_strip_spec(
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F]) == seq![0x66, 0x6F, 0x6F]);
        gi_slot_one_miss(
            ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false,
            seq![0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        // the ".gitignore" line "!foo" hits
        assert(gi_strip_spec(
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F]) == seq![0x66, 0x6F, 0x6F]);
        gi_slot_one_eval(
            ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false,
            seq![0x66, 0x6F, 0x6F],
            true,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        // the exclude store misses "foo" on BOTH lines
        assert(gi_strip_spec(
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F]) == seq![0x66, 0x6F, 0x6F]);
        gi_slot_two_miss(
            ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false,
            seq![0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x7A],
        );
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x66, 0x6F, 0x6F], false, true)
            == MiScanSt {
                m_custom: None,
                m_ignore: None,
                m_gi: Some((true, IgmOrigSpec::Gi((
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    true, false, None)))),
                m_gi_exclude: None,
                saw_git: true,
            });
        assert(ig.absolute_base@ matches None);
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        assert(ig.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            seq![0x66, 0x6F, 0x6F], false) == None);
        assert(dir_mi_spec(&ig, seq![0x66, 0x6F, 0x6F], false)
            == Some((true, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                true, false, None)))));
    }
    let m1 = ig.matched(b_foo().as_slice(), false);
    assert(ig_m_view(&m1)
        == Some((true, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], true, false, None)))));
    assert(m1 matches Match::Whitelist(_));

    // candidate "bar": whitelisted by ".ignore" "!bar"; the exclude
    // store's idx0 line also matches but loses the cascade
    proof {
        assert(gi_strip_spec(
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72]) == seq![0x62, 0x61, 0x72]);
        gi_slot_one_eval(
            ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false,
            seq![0x62, 0x61, 0x72],
            true,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        assert(gi_strip_spec(
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72]) == seq![0x62, 0x61, 0x72]);
        gi_slot_one_miss(
            ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false,
            seq![0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        assert(gi_strip_spec(
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72]) == seq![0x62, 0x61, 0x72]);
        gi_slot_two_fall_hit(
            ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false,
            seq![0x62, 0x61, 0x72],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x7A],
        );
        assert(dir_mi_spec(&ig, seq![0x62, 0x61, 0x72], false)
            == Some((true, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8],
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                true, false, None)))));
    }
    let m2 = ig.matched(b_bar().as_slice(), false);
    assert(ig_m_view(&m2)
        == Some((true, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], true, false, None)))));
    assert(m2 matches Match::Whitelist(_));

    // candidate "baz": only the exclude pool decides
    proof {
        assert(gi_strip_spec(
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A]) == seq![0x62, 0x61, 0x7A]);
        gi_slot_one_miss(
            ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false,
            seq![0x62, 0x61, 0x7A],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        assert(gi_strip_spec(
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A]) == seq![0x62, 0x61, 0x7A]);
        gi_slot_one_miss(
            ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false,
            seq![0x62, 0x61, 0x7A],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        assert(gi_strip_spec(
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A]) == seq![0x62, 0x61, 0x7A]);
        gi_slot_two_high_hit(
            ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false,
            seq![0x62, 0x61, 0x7A],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x7A],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x7A],
        );
        assert(dir_mi_spec(&ig, seq![0x62, 0x61, 0x7A], false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x7Au8],
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x7A],
                false, false, None)))));
    }
    let m3 = ig.matched(b_baz().as_slice(), false);
    assert(ig_m_view(&m3)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x7Au8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x7Au8], false, false, None)))));
    assert(m3 matches Match::Ignore(_));
    true
}

/// git_exclude (dir.rs:1191-1201): the .git/info/exclude pool alone:
/// foo ignored, bar whitelisted (the "!bar" line decides over the
/// masked-out... the "foo" line below it), baz unmatched.
fn row_git_exclude() -> (r: bool)
    ensures r
{
    let excl_m = h_matcher2(b_td_root(), b_ss_foo(), false, false,
        b_ss_bar(), true, false);
    let head_e_custom = h_empty();
    let head_e_ignore = h_empty();
    let head_e_gi = h_empty();
    let head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: head_e_custom,
        ignore_matcher: head_e_ignore,
        git_ignore_matcher: head_e_gi,
        git_exclude_matcher: excl_m,
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: None };
    assert(ig_wf(&ig));

    // the mask admits (S14 columns line"foo" / line"!bar" / line"bar")
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x66, 0x6F, 0x6F]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x66, 0x6F, 0x6F]) == true);

    proof {
        assert(ig.nodes@ == seq![head, rootnd]);
        assert(ig.nodes@[0] == head);
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(first_abs, 4);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 3);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        assert(ig.nodes@.len() == 2);
        assert(first_abs(ig.nodes@, 0) == 1);
        assert(ig.inner.opts.require_git == true);
        assert(any_has_git(ig.nodes@, 0) == true);
        assert(ig_any_git(&ig) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        assert(gi_strip_spec(
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F]) == seq![0x66, 0x6F, 0x6F]);
        gi_slot_two_fall_hit(
            ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false,
            seq![0x66, 0x6F, 0x6F],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x66, 0x6F, 0x6F], false, true)
            == MiScanSt {
                m_custom: None,
                m_ignore: None,
                m_gi: None,
                m_gi_exclude: Some((false, IgmOrigSpec::Gi((
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    false, false, None)))),
                saw_git: true,
            });
        assert(ig.absolute_base@ matches None);
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        assert(ig.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            seq![0x66, 0x6F, 0x6F], false) == None);
        assert(dir_mi_spec(&ig, seq![0x66, 0x6F, 0x6F], false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
    }
    let m1 = ig.matched(b_foo().as_slice(), false);
    assert(ig_m_view(&m1)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], false, false, None)))));
    assert(m1 matches Match::Ignore(_));

    // candidate "bar": the LATER "!bar" line decides
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x62, 0x61, 0x72]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x62, 0x61, 0x72]) == true);
    proof {
        assert(gi_strip_spec(
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72]) == seq![0x62, 0x61, 0x72]);
        gi_slot_two_high_hit(
            ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false,
            seq![0x62, 0x61, 0x72],
            true,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        assert(dir_mi_spec(&ig, seq![0x62, 0x61, 0x72], false)
            == Some((true, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8],
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                true, false, None)))));
    }
    let m2 = ig.matched(b_bar().as_slice(), false);
    assert(ig_m_view(&m2)
        == Some((true, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], true, false, None)))));
    assert(m2 matches Match::Whitelist(_));

    // candidate "baz": both exclude lines miss
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x62, 0x61, 0x7A]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x62, 0x61, 0x7A]) == false);
    proof {
        assert(gi_strip_spec(
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A]) == seq![0x62, 0x61, 0x7A]);
        gi_slot_two_miss(
            ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x7A], false,
            seq![0x62, 0x61, 0x7A],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        assert(dir_mi_spec(&ig, seq![0x62, 0x61, 0x7A], false) == None);
    }
    let m3 = ig.matched(b_baz().as_slice(), false);
    assert(ig_m_view(&m3) == None);
    assert(m3 matches Match::None);
    true
}

/// stops_at_git_dir (dir.rs:1395-1416): .gitignore files beyond a
/// .git barrier are not matched (ig2's foo -> None), but .ignore
/// files are (ig2's bar -> Ignore); ig1, ending AT the .git dir,
/// matches both (upstream: "This tests that .gitignore files beyond
/// a .git barrier aren't matched, but .ignore files are.").
fn row_stops_at_git_dir() -> (r: bool)
    ensures r
{
    // the td stores: ".gitignore" line "foo", ".ignore" line "bar"
    let td_gi = h_matcher1(b_td_root(), b_ss_foo(), false, false);
    let td_ig = h_matcher1(b_td_root(), b_ss_bar(), false, false);
    // ig1: the stack ending at td (the node that CONTAINS .git)
    let ig1_head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: td_ig,
        git_ignore_matcher: td_gi,
        git_exclude_matcher: h_empty(),
    };
    let ig1_root = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let ig1_inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns1: Vec<IgnoreNode> = Vec::new();
    ns1.push(ig1_head);
    ns1.push(ig1_root);
    let ig1 = Ignore { inner: ig1_inner, nodes: ns1, absolute_base: None };
    assert(ig_wf(&ig1));
    // ig2: the child stack, one node below td (upstream adds
    // ig1.path().join("foo"), a directory with its own .git)
    let ig2_head = IgnoreNode {
        dir: b_foo(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let td_ig2 = h_matcher1(b_td_root(), b_ss_bar(), false, false);
    let td_gi2 = h_matcher1(b_td_root(), b_ss_foo(), false, false);
    let ig2_td = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: td_ig2,
        git_ignore_matcher: td_gi2,
        git_exclude_matcher: h_empty(),
    };
    let ig2_root = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let ov_e2 = Override::empty();
    let types_e2 = Types::empty();
    let gg_e2 = h_empty();
    let opts2 = h_opts_default();
    let ig2_inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e2,
        types: types_e2,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e2,
        opts: opts2,
    };
    let mut ns2: Vec<IgnoreNode> = Vec::new();
    ns2.push(ig2_head);
    ns2.push(ig2_td);
    ns2.push(ig2_root);
    let ig2 = Ignore { inner: ig2_inner, nodes: ns2, absolute_base: None };
    assert(ig_wf(&ig2));

    // the mask admits (S14 columns line"foo" / line"bar")
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x66, 0x6F, 0x6F]) == true);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x62, 0x61, 0x72]) == true);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x66, 0x6F, 0x6F]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x62, 0x61, 0x72]) == false);

    // ig1.matched("foo") == Ignore (the td .gitignore applies)
    proof {
        assert(ig1.nodes@ == seq![ig1_head, ig1_root]);
        assert(ig1.nodes@[0] == ig1_head);
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(first_abs, 4);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 3);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        assert(ig1.nodes@.len() == 2);
        assert(first_abs(ig1.nodes@, 0) == 1);
        assert(ig1.inner.opts.require_git == true);
        assert(any_has_git(ig1.nodes@, 0) == true);
        assert(ig_any_git(&ig1) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig1) == true);
        gi_slot_empty_eval(ig1.nodes@[0].custom_ignore_matcher.globs@,
            ig1.nodes@[0].custom_ignore_matcher.set.registered@,
            ig1.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        assert(gi_strip_spec(
            ig1.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F]) == seq![0x66, 0x6F, 0x6F]);
        gi_slot_one_miss(
            ig1.nodes@[0].ignore_matcher.globs@,
            ig1.nodes@[0].ignore_matcher.set.registered@,
            ig1.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false,
            seq![0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        assert(gi_strip_spec(
            ig1.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F]) == seq![0x66, 0x6F, 0x6F]);
        gi_slot_one_eval(
            ig1.nodes@[0].git_ignore_matcher.globs@,
            ig1.nodes@[0].git_ignore_matcher.set.registered@,
            ig1.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false,
            seq![0x66, 0x6F, 0x6F],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        gi_slot_empty_eval(ig1.nodes@[0].git_exclude_matcher.globs@,
            ig1.nodes@[0].git_exclude_matcher.set.registered@,
            ig1.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        assert(mi_scan(ig1.nodes@, 0, 1, mi_st_none(),
            seq![0x66, 0x6F, 0x6F], false, true)
            == MiScanSt {
                m_custom: None,
                m_ignore: None,
                m_gi: Some((false, IgmOrigSpec::Gi((
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    false, false, None)))),
                m_gi_exclude: None,
                saw_git: true,
            });
        assert(ig1.absolute_base@ matches None);
        gi_slot_empty_eval(ig1.inner.git_global_matcher.globs@,
            ig1.inner.git_global_matcher.set.registered@,
            ig1.inner.git_global_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        assert(ig1.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig1.inner.explicit_ignores@, -1,
            seq![0x66, 0x6F, 0x6F], false) == None);
        assert(dir_mi_spec(&ig1, seq![0x66, 0x6F, 0x6F], false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
    }
    let m1 = ig1.matched(b_foo().as_slice(), false);
    assert(ig_m_view(&m1)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], false, false, None)))));
    assert(m1 matches Match::Ignore(_));

    // ig1.matched("bar") == Ignore (the td .ignore applies)
    proof {
        assert(gi_strip_spec(
            ig1.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72]) == seq![0x62, 0x61, 0x72]);
        gi_slot_one_eval(
            ig1.nodes@[0].ignore_matcher.globs@,
            ig1.nodes@[0].ignore_matcher.set.registered@,
            ig1.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false,
            seq![0x62, 0x61, 0x72],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        assert(dir_mi_spec(&ig1, seq![0x62, 0x61, 0x72], false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8],
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                false, false, None)))));
    }
    let m2 = ig1.matched(b_bar().as_slice(), false);
    assert(ig_m_view(&m2)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], false, false, None)))));
    assert(m2 matches Match::Ignore(_));

    // ig2.matched("foo") == None: the td .gitignore sits beyond the
    // child's own .git barrier (saw_git)
    proof {
        assert(ig2.nodes@ == seq![ig2_head, ig2_td, ig2_root]);
        assert(ig2.nodes@[0] == ig2_head);
        assert(ig2.nodes@[1] == ig2_td);
        reveal_with_fuel(mi_scan, 4);
        assert(ig2.nodes@.len() == 3);
        assert(first_abs(ig2.nodes@, 0) == 2);
        assert(ig2.inner.opts.require_git == true);
        assert(any_has_git(ig2.nodes@, 0) == true);
        assert(ig_any_git(&ig2) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig2) == true);
        gi_slot_empty_eval(ig2.nodes@[0].custom_ignore_matcher.globs@,
            ig2.nodes@[0].custom_ignore_matcher.set.registered@,
            ig2.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig2.nodes@[0].ignore_matcher.globs@,
            ig2.nodes@[0].ignore_matcher.set.registered@,
            ig2.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig2.nodes@[0].git_ignore_matcher.globs@,
            ig2.nodes@[0].git_ignore_matcher.set.registered@,
            ig2.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig2.nodes@[0].git_exclude_matcher.globs@,
            ig2.nodes@[0].git_exclude_matcher.set.registered@,
            ig2.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        assert(mi_step(ig2_head, mi_st_none(),
            seq![0x66, 0x6F, 0x6F], false, true)
            == MiScanSt {
                m_custom: None,
                m_ignore: None,
                m_gi: None,
                m_gi_exclude: None,
                saw_git: true,
            });
        // the td step: an .ignore still consults; the .gitignore is
        // now BEHIND the saw_git barrier (dir.rs:609-615's gate)
        assert(gi_strip_spec(
            ig2.nodes@[1].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F]) == seq![0x66, 0x6F, 0x6F]);
        gi_slot_one_miss(
            ig2.nodes@[1].ignore_matcher.globs@,
            ig2.nodes@[1].ignore_matcher.set.registered@,
            ig2.nodes@[1].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false,
            seq![0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        let st_mid = MiScanSt {
            m_custom: None,
            m_ignore: None,
            m_gi: None,
            m_gi_exclude: None,
            saw_git: true,
        };
        assert(mi_step(ig2_td, st_mid,
            seq![0x66, 0x6F, 0x6F], false, true) == st_mid);
        assert(mi_scan(ig2.nodes@, 0, 2, mi_st_none(),
            seq![0x66, 0x6F, 0x6F], false, true) == st_mid);
        assert(ig2.absolute_base@ matches None);
        gi_slot_empty_eval(ig2.inner.git_global_matcher.globs@,
            ig2.inner.git_global_matcher.set.registered@,
            ig2.inner.git_global_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        assert(ig2.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig2.inner.explicit_ignores@, -1,
            seq![0x66, 0x6F, 0x6F], false) == None);
        assert(dir_mi_spec(&ig2, seq![0x66, 0x6F, 0x6F], false) == None);
    }
    let m3 = ig2.matched(b_foo().as_slice(), false);
    assert(ig_m_view(&m3) == None);
    assert(m3 matches Match::None);

    // ig2.matched("bar") == Ignore: the td .ignore consults through
    proof {
        assert(gi_strip_spec(
            ig2.nodes@[1].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72]) == seq![0x62, 0x61, 0x72]);
        gi_slot_one_eval(
            ig2.nodes@[1].ignore_matcher.globs@,
            ig2.nodes@[1].ignore_matcher.set.registered@,
            ig2.nodes@[1].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false,
            seq![0x62, 0x61, 0x72],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        let st_b = MiScanSt {
            m_custom: None,
            m_ignore: Some((false, IgmOrigSpec::Gi((
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                false, false, None)))),
            m_gi: None,
            m_gi_exclude: None,
            saw_git: true,
        };
        assert(mi_step(ig2_td, MiScanSt {
            m_custom: None,
            m_ignore: None,
            m_gi: None,
            m_gi_exclude: None,
            saw_git: true,
        }, seq![0x62, 0x61, 0x72], false, true) == st_b);
        assert(mi_scan(ig2.nodes@, 0, 2, mi_st_none(),
            seq![0x62, 0x61, 0x72], false, true) == st_b);
        assert(ig2.absolute_base@ matches None);
        gi_slot_empty_eval(ig2.inner.git_global_matcher.globs@,
            ig2.inner.git_global_matcher.set.registered@,
            ig2.inner.git_global_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        assert(mi_explicit(ig2.inner.explicit_ignores@, -1,
            seq![0x62, 0x61, 0x72], false) == None);
        assert(dir_mi_spec(&ig2, seq![0x62, 0x61, 0x72], false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8],
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                false, false, None)))));
    }
    let m4 = ig2.matched(b_bar().as_slice(), false);
    assert(ig_m_view(&m4)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], false, false, None)))));
    assert(m4 matches Match::Ignore(_));
    true
}

/// custom_ignore_precedence (dir.rs:1302-1316): "Tests that earlier
/// custom ignore files have lower precedence than later." -- two
/// custom files, the first carrying "foo", the second "!foo": the
/// LATER (higher store index) decides, so foo is whitelisted, with
/// the origin in the custom slot.
fn row_custom_precedence() -> (r: bool)
    ensures r
{
    // one custom store: idx0 = file1's "foo" line, idx1 = file2's
    // "!foo" line (the per-file append order, dir.rs:1039-1082)
    let custom_m = h_matcher2(b_td_root(), b_ss_foo(), false, false,
        b_ss_foo(), true, false);
    let head_e_ignore = h_empty();
    let head_e_gi = h_empty();
    let head_e_excl = h_empty();
    let head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: custom_m,
        ignore_matcher: head_e_ignore,
        git_ignore_matcher: head_e_gi,
        git_exclude_matcher: head_e_excl,
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let mut custom_names: Vec<Vec<u8>> = Vec::new();
    custom_names.push(b_xcustom());
    custom_names.push(b_xcustom());
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: custom_names,
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: None };
    assert(ig_wf(&ig));

    // the mask admit (S14 column line"!foo": foo=1 -- BOTH custom
    // lines carry the same actual)
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x66, 0x6F, 0x6F]) == true);

    proof {
        assert(ig.nodes@ == seq![head, rootnd]);
        assert(ig.nodes@[0] == head);
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(first_abs, 4);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 3);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        assert(ig.nodes@.len() == 2);
        assert(first_abs(ig.nodes@, 0) == 1);
        assert(ig.inner.opts.require_git == true);
        assert(any_has_git(ig.nodes@, 0) == false);
        assert(ig_any_git(&ig) == false);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false);
        assert(gi_strip_spec(
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F]) == seq![0x66, 0x6F, 0x6F]);
        // BOTH lines hit; the scan starts at the TOP, so the LATER
        // "!foo" line decides
        gi_slot_two_top_hit(
            ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x66, 0x6F, 0x6F], false,
            seq![0x66, 0x6F, 0x6F],
            true,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x66, 0x6F, 0x6F], false, false)
            == MiScanSt {
                m_custom: Some((true, IgmOrigSpec::Gi((
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    true, false, None)))),
                m_ignore: None,
                m_gi: None,
                m_gi_exclude: None,
                saw_git: false,
            });
        assert(ig.absolute_base@ matches None);
        assert(ig.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            seq![0x66, 0x6F, 0x6F], false) == None);
        assert(dir_mi_spec(&ig, seq![0x66, 0x6F, 0x6F], false)
            == Some((true, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                true, false, None)))));
    }
    let m = ig.matched(b_foo().as_slice(), false);
    assert(ig_m_view(&m)
        == Some((true, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], true, false, None)))));
    assert(m matches Match::Whitelist(_));
    true
}
/// absolute_parent (dir.rs:1418-1439), the baseline half: "First,
/// check that the parent gitignore file isn't detected if the parent
/// isn't added." -- the child stack alone leaves "bar" unmatched
/// (upstream ig1.matched("bar") is None, dir.rs:1427-1430).
fn row_abs_parent_baseline() -> (r: bool)
    ensures r
{
    let head_e_custom = h_empty();
    let head_e_ignore = h_empty();
    let head_e_gi = h_empty();
    let head_e_excl = h_empty();
    let head = IgnoreNode {
        dir: b_slash_td_foo(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: head_e_custom,
        ignore_matcher: head_e_ignore,
        git_ignore_matcher: head_e_gi,
        git_exclude_matcher: head_e_excl,
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: None };
    assert(ig_wf(&ig));
    proof {
        // the mask admit (S14 column line"bar": foo=0)
        assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x66, 0x6F, 0x6F]) == false);
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(first_abs, 4);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 3);
        reveal(iglib::pathutil::is_file_name_spec);
        assert(ig.nodes@ == seq![head, rootnd]);
        assert(ig.nodes@[0] == head);
        assert(ig.nodes@[1] == rootnd);
        assert(first_abs(ig.nodes@, 0) == 1);
        assert(ig_any_git(&ig) == false);
        // rung 1: the head's four empty slots
        assert(head.custom_ignore_matcher == head_e_custom);
        assert(head.ignore_matcher == head_e_ignore);
        assert(head.git_ignore_matcher == head_e_gi);
        assert(head.git_exclude_matcher == head_e_excl);
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x62, 0x61, 0x72], false, false) == mi_st_none());
        // rung 2: the second-scan gate is clearly CLOSED
        assert(ig.absolute_base@ matches None);
        // rung 3: the global store is empty
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        // rung 4: the explicit pool is empty
        assert(ig.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            seq![0x62, 0x61, 0x72], false) == None);
        // rung 5: the cascade is empty
        assert(dir_mi_spec(&ig, seq![0x62, 0x61, 0x72], false) == None);
    }
    let m = ig.matched(b_bar().as_slice(), false);
    assert(ig_m_view(&m) == None);
    assert(m matches Match::None);
    true
}

/// absolute_parent (dir.rs:1418-1439), the attach half: "Second,
/// check that adding a parent directory actually works." -- the
/// rewrite joins the abs base, so the parent's .gitignore "bar"
/// (actual "**/bar") decides Ignore on the joined path
/// (upstream ig2.matched("bar") is Ignore, dir.rs:1432-1438).
fn row_abs_parent_attach() -> (r: bool)
    ensures r
{
    // the parent's .gitignore: line "bar" (actual "**/bar"), root "/td"
    let parent_gi = h_matcher1(b_slash_td(), b_ss_bar(), false, false);
    let head_e_custom = h_empty();
    let head_e_ignore = h_empty();
    let head_e_gi = h_empty();
    let head_e_excl = h_empty();
    let head = IgnoreNode {
        dir: b_slash_td_foo(),
        is_absolute_parent: false,
        has_absolute_parent_rules: true,
        has_git: false,
        custom_ignore_matcher: head_e_custom,
        ignore_matcher: head_e_ignore,
        git_ignore_matcher: head_e_gi,
        git_exclude_matcher: head_e_excl,
    };
    let parent_e_custom = h_empty();
    let parent_e_ignore = h_empty();
    let parent_e_excl = h_empty();
    let parent = IgnoreNode {
        dir: b_slash_td(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: parent_e_custom,
        ignore_matcher: parent_e_ignore,
        git_ignore_matcher: parent_gi,
        git_exclude_matcher: parent_e_excl,
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(parent);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns,
        absolute_base: Some(b_slash_td_foo()) };
    assert(ig_wf(&ig));
    proof {
        // the mask admit (S14 column line"bar": foo/bar=1 -- the
        // joined candidate "foo/bar" spell)
        assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72]) == true);
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(first_abs, 5);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 4);
        reveal_with_fuel(append_prefix, 8);
        reveal(join_bytes);
        reveal(mi_rewrite);
        reveal(iglib::pathutil::strip_prefix_spec);
        reveal(iglib::pathutil::bytes_prefix_eq);
        reveal(iglib::pathutil::is_file_name_spec);
        assert(ig.nodes@ == seq![head, parent, rootnd]);
        assert(ig.nodes@[0] == head);
        assert(ig.nodes@[1] == parent);
        assert(ig.nodes@[2] == rootnd);
        assert(first_abs(ig.nodes@, 0) == 1);
        assert(ig_any_git(&ig) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        // rung 1: the head's four empty slots, first scan over [0..1)
        assert(head.custom_ignore_matcher == head_e_custom);
        assert(head.ignore_matcher == head_e_ignore);
        assert(head.git_ignore_matcher == head_e_gi);
        assert(head.git_exclude_matcher == head_e_excl);
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x62, 0x61, 0x72], false, true) == mi_st_none());
        // rung 2: the rewrite: strip "./" (no-op), strip the head dir
        // (no prefix of the bare candidate), strip "/" (no-op), join
        // the abs base
        assert(strip_keep(seq![0x2E, 0x2F], seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F])
            == seq![0x2Fu8, 0x74u8, 0x64u8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8]);
        assert(strip_keep(seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F], seq![0x62, 0x61, 0x72])
            == seq![0x62u8, 0x61u8, 0x72u8]);
        assert(strip_keep(seq![0x2F], seq![0x62, 0x61, 0x72]) == seq![0x62, 0x61, 0x72]);
        // the join is byte-literal: append_prefix chains the pushes
        assert(join_bytes(seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x62, 0x61, 0x72])
            == append_prefix(seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F].push(0x2F),
                seq![0x62, 0x61, 0x72], 3));
        let s0 = seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F].push(0x2F);
        let rel: Seq<u8> = seq![0x62, 0x61, 0x72];
        assert(append_prefix(s0, rel, 0) == s0);
        assert(append_prefix(s0, rel, 1) == s0.push(rel[0]));
        assert(append_prefix(s0, rel, 2) == s0.push(rel[0]).push(rel[1]));
        assert(append_prefix(s0, rel, 3) == s0.push(rel[0]).push(rel[1]).push(rel[2]));
        assert(s0.len() == 8);
        seq_ext_eq(s0,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F, 0x2F]);
        seq_ext_eq(s0.push(rel[0]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62,
                0x61]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]).push(rel[2]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62,
                0x61, 0x72]);
        assert(mi_rewrite(ig.nodes@, seq![0x62, 0x61, 0x72],
            seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F])
            == seq![0x2Fu8, 0x74u8, 0x64u8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8]);
        // rung 3: the second scan: the parent's .gitignore hits; the
        // root-tail node after it keeps the state (saw_git set)
        assert(parent.git_ignore_matcher == parent_gi);
        assert(parent.custom_ignore_matcher == parent_e_custom);
        assert(parent.ignore_matcher == parent_e_ignore);
        assert(parent.git_exclude_matcher == parent_e_excl);
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F,
            0x6F, 0x2F, 0x62, 0x61, 0x72];
        gi_slot_empty_eval(parent.custom_ignore_matcher.globs@,
            parent.custom_ignore_matcher.set.registered@,
            parent.custom_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent.ignore_matcher.globs@,
            parent.ignore_matcher.set.registered@,
            parent.ignore_matcher.root.bytes@,
            path2, false);
assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72]);
gstrip_p3t7(0x2F, 0x74, 0x64, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, path2);


        gi_slot_one_eval(
            parent.git_ignore_matcher.globs@,
            parent.git_ignore_matcher.set.registered@,
            parent.git_ignore_matcher.root.bytes@,
            path2,
            false,
            seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        gi_slot_empty_eval(parent.git_exclude_matcher.globs@,
            parent.git_exclude_matcher.set.registered@,
            parent.git_exclude_matcher.root.bytes@,
            path2, false);
        // the parent step's resulting state (saw_git set)
        let st_mid = MiScanSt {
            m_custom: None,
            m_ignore: None,
            m_gi: Some((false, IgmOrigSpec::Gi((
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                false, false, None)))),
            m_gi_exclude: None,
            saw_git: true,
        };
        assert(mi_step(parent, mi_st_none(), path2, false, true)
            == st_mid);
        // the root-tail step keeps the state (empty stores; saw_git
        // stays set)
        assert(mi_step(rootnd, st_mid, path2, false, true) == st_mid);
        assert(mi_scan(ig.nodes@, 1, 3, mi_st_none(), path2, false,
            true) == st_mid);
        // rung 4: the global store is empty; the explicit pool is empty
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            seq![0x62, 0x61, 0x72], false);
        assert(ig.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            seq![0x62, 0x61, 0x72], false) == None);
        // rung 5: the cascade
        assert(dir_mi_spec(&ig, seq![0x62, 0x61, 0x72], false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8],
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                false, false, None)))));
    }
    let m = ig.matched(b_bar().as_slice(), false);
    assert(ig_m_view(&m)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
            false, false, None)))));
    assert(m matches Match::Ignore(_));
    true
}

/// absolute_parent_anchored (dir.rs:1441-1459), re-spelled onto the
/// S14 palette: the upstream lines "/llvm/\nfoo" and the root
/// candidates (llvm, src/llvm, foo, src/foo) become the parent
/// lines "/foo\nfoo" (idx0 anchored actual "foo", idx1 plain
/// actual "**/foo") with the search root "x" containing dir "y":
/// the anchored line never reaches across the root-join depth (the
/// joined path strips to "x/y/bar", which the anchored "foo" does
/// not match) while the plain line hits "x/y/foo" in the bare
/// spelling (the twin covers the bare mouth spellings "y/foo" /
/// "y/bar" -- the head-strip cleanly misses them, the join restores
/// the root name). The anchored MISSING pairs are ANALOG admits:
/// the S14 anchored family is line"/foo" (foo/bar=0, x/y/foo=0)
/// and the plain family line"foo" (sub/x/y=0) -- quoted for the
/// component shapes, not for the exact x/y/bar spelling.
fn row_abs_parent_anchored() -> (r: bool)
    ensures r
{
    // the parents-only stack (upstream ig1): [parent, builder root]
    let parent_gi = h_matcher2(b_slash_td(), b_foo(), false, false,
        b_ss_foo(), false, false);
    let parent = IgnoreNode {
        dir: b_slash_td(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: parent_gi,
        git_exclude_matcher: h_empty(),
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let ig1_inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns1: Vec<IgnoreNode> = Vec::new();
    ns1.push(parent);
    ns1.push(rootnd);
    let ig1 = Ignore { inner: ig1_inner, nodes: ns1,
        absolute_base: Some(b_slash_td_x()) };
    assert(ig_wf(&ig1));

    // the search-root stack (upstream ig2, add_child of the root x):
    // [head "x", parent, builder root]
    let head_x = IgnoreNode {
        dir: b_x(),
        is_absolute_parent: false,
        has_absolute_parent_rules: true,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let parent_gi2 = h_matcher2(b_slash_td(), b_foo(), false, false,
        b_ss_foo(), false, false);
    let parent2 = IgnoreNode {
        dir: b_slash_td(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: parent_gi2,
        git_exclude_matcher: h_empty(),
    };
    let rootnd2 = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e2 = Types::empty();
    let ov_e2 = Override::empty();
    let gg_e2 = h_empty();
    let opts2 = h_opts_default();
    let ig2_inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e2,
        types: types_e2,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e2,
        opts: opts2,
    };
    let mut ns2: Vec<IgnoreNode> = Vec::new();
    ns2.push(head_x);
    ns2.push(parent2);
    ns2.push(rootnd2);
    let ig2 = Ignore { inner: ig2_inner, nodes: ns2,
        absolute_base: Some(b_slash_td_x()) };
    assert(ig_wf(&ig2));

    // the mask admits: ONE exact (S14 line"foo": x/y/foo=1) and two
    // ANALOG misses for the anchored/plain families
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F]) == true);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72]) == false);
    assume(glob_pat_matches(seq![0x66, 0x6F, 0x6F], false, seq![0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72]) == false);

    // ig1.matched("y/bar", true) == None: no relative node above
    // the barrier, so the candidate is joined whole and both store
    // lines miss the depth (upstream ig1.matched("llvm", true))
    proof {
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(append_prefix, 8);
        reveal(join_bytes);
        reveal(mi_rewrite);
        reveal(iglib::pathutil::strip_prefix_spec);
        reveal(iglib::pathutil::bytes_prefix_eq);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        reveal_with_fuel(first_abs, 5);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 4);
        assert(ig1.nodes@ == seq![parent, rootnd]);
        assert(ig1.nodes@[0] == parent);
        assert(ig1.nodes@[1] == rootnd);
        assert(first_abs(ig1.nodes@, 0) == 0);
        assert(ig_any_git(&ig1) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig1) == true);
        // the rewrite: b == 0, so the bare candidate is joined whole
        let cand: Seq<u8> = seq![0x79, 0x2F, 0x62, 0x61, 0x72];
        let s0 = seq![0x2F, 0x74, 0x64, 0x2F, 0x78].push(0x2F);
        let rel: Seq<u8> = cand;
        assert(join_bytes(seq![0x2F, 0x74, 0x64, 0x2F, 0x78], rel)
            == append_prefix(s0, rel, 5));
        assert(append_prefix(s0, rel, 0) == s0);
        assert(append_prefix(s0, rel, 1) == s0.push(rel[0]));
        assert(append_prefix(s0, rel, 2) == s0.push(rel[0]).push(rel[1]));
        assert(append_prefix(s0, rel, 3)
            == s0.push(rel[0]).push(rel[1]).push(rel[2]));
        assert(append_prefix(s0, rel, 4)
            == s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3]));
        assert(append_prefix(s0, rel, 5)
            == s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]));
        assert(s0.len() == 6);
        seq_ext_eq(s0, seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F]);
        seq_ext_eq(s0.push(rel[0]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]).push(rel[2]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F, 0x62]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F, 0x62,
                0x61]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F, 0x62,
                0x61, 0x72]);
        assert(mi_rewrite(ig1.nodes@, cand,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78])
            == seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F,
                0x62, 0x61, 0x72]);
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F,
            0x79, 0x2F, 0x62, 0x61, 0x72];
        assert(bytes_prefix_eq(seq![0x2Fu8, 0x74u8, 0x64u8], path2));
assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2) == seq![0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72]);
gstrip_p3t7(0x2F, 0x74, 0x64, 0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72, path2);


        // both store lines miss the depth: the plain "**/foo" and
        // the anchored "foo"
        gi_slot_two_miss(
            parent.git_ignore_matcher.globs@,
            parent.git_ignore_matcher.set.registered@,
            parent.git_ignore_matcher.root.bytes@,
            path2, true,
            seq![0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72],
            seq![0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        gi_slot_empty_eval(parent.custom_ignore_matcher.globs@,
            parent.custom_ignore_matcher.set.registered@,
            parent.custom_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent.ignore_matcher.globs@,
            parent.ignore_matcher.set.registered@,
            parent.ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent.git_exclude_matcher.globs@,
            parent.git_exclude_matcher.set.registered@,
            parent.git_exclude_matcher.root.bytes@,
            path2, false);
        let st_a = MiScanSt {
            m_custom: None,
            m_ignore: None,
            m_gi: None,
            m_gi_exclude: None,
            saw_git: true,
        };
        assert(mi_step(parent, mi_st_none(), path2, true, true)
            == st_a);
        assert(mi_step(rootnd, st_a, path2, true, true) == st_a);
        assert(mi_scan(ig1.nodes@, 0, 2, mi_st_none(), path2, true,
            true) == st_a);
        gi_slot_empty_eval(ig1.inner.git_global_matcher.globs@,
            ig1.inner.git_global_matcher.set.registered@,
            ig1.inner.git_global_matcher.root.bytes@,
            cand, true);
        assert(ig1.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig1.inner.explicit_ignores@, -1,
            cand, true) == None);
        assert(dir_mi_spec(&ig1, cand, true) == None);
    }
    let m1 = ig1.matched(b_y_bar().as_slice(), true);
    assert(ig_m_view(&m1) == None);
    assert(m1 matches Match::None);

    // ig2.matched("y/foo", false) == Ignore (upstream foo): the
    // head-strip misses the bare spelling, the join restores the
    // root name "x", and the plain line hits "x/y/foo"
    proof {
        assert(ig2.nodes@ == seq![head_x, parent2, rootnd2]);
        assert(ig2.nodes@[0] == head_x);
        assert(ig2.nodes@[1] == parent2);
        assert(ig2.nodes@[2] == rootnd2);
        assert(first_abs(ig2.nodes@, 0) == 1);
        assert(ig_any_git(&ig2) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig2) == true);
        let cand: Seq<u8> = seq![0x79, 0x2F, 0x66, 0x6F, 0x6F];
        // the first scan over the empty "x" head
        gi_slot_empty_eval(ig2.nodes@[0].custom_ignore_matcher.globs@,
            ig2.nodes@[0].custom_ignore_matcher.set.registered@,
            ig2.nodes@[0].custom_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(ig2.nodes@[0].ignore_matcher.globs@,
            ig2.nodes@[0].ignore_matcher.set.registered@,
            ig2.nodes@[0].ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(ig2.nodes@[0].git_ignore_matcher.globs@,
            ig2.nodes@[0].git_ignore_matcher.set.registered@,
            ig2.nodes@[0].git_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(ig2.nodes@[0].git_exclude_matcher.globs@,
            ig2.nodes@[0].git_exclude_matcher.set.registered@,
            ig2.nodes@[0].git_exclude_matcher.root.bytes@,
            cand, false);
        assert(mi_scan(ig2.nodes@, 0, 1, mi_st_none(), cand, false,
            true) == mi_st_none());
        // the head-strip misses the bare spelling; the join lands on
        // "/td/x/y/foo"
        assert(strip_keep(seq![0x2E, 0x2F], seq![0x78]) == seq![0x78]);
        assert(strip_keep(seq![0x78], cand) == cand);
        strip_keep_nostrip(cand);
        assert(strip_keep(seq![0x2Fu8], cand) == cand);
        let s0 = seq![0x2F, 0x74, 0x64, 0x2F, 0x78].push(0x2F);
        let rel: Seq<u8> = cand;
        assert(join_bytes(seq![0x2F, 0x74, 0x64, 0x2F, 0x78], rel)
            == append_prefix(s0, rel, 5));
        assert(append_prefix(s0, rel, 5)
            == s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]));
        seq_ext_eq(s0, seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F, 0x66,
                0x6F, 0x6F]);
        assert(mi_rewrite(ig2.nodes@, cand,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78])
            == seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F,
                0x66, 0x6F, 0x6F]);
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F,
            0x79, 0x2F, 0x66, 0x6F, 0x6F];
        // the scalar strip helper FIRST (its ensures supplies the
        // strip facts; the asserts below are the trivialisations)
        gstrip_p3t7(0x2F, 0x74, 0x64, 0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F, path2);
        assert(bytes_prefix_eq(seq![0x2Fu8, 0x74u8, 0x64u8], path2));
        assert(strip_prefix_spec(seq![0x2F, 0x74, 0x64], path2)
            == Some(seq![0x2F, 0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F,
                0x6F]));
        assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2)
            == seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F]);


        // the store scan starts at the TOP: the plain "**/foo" line
        // decides before the anchored "foo"
        gi_slot_two_top_hit(
            parent2.git_ignore_matcher.globs@,
            parent2.git_ignore_matcher.set.registered@,
            parent2.git_ignore_matcher.root.bytes@,
            path2, false,
            seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        gi_slot_empty_eval(parent2.custom_ignore_matcher.globs@,
            parent2.custom_ignore_matcher.set.registered@,
            parent2.custom_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent2.ignore_matcher.globs@,
            parent2.ignore_matcher.set.registered@,
            parent2.ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent2.git_exclude_matcher.globs@,
            parent2.git_exclude_matcher.set.registered@,
            parent2.git_exclude_matcher.root.bytes@,
            path2, false);
        let st_b = MiScanSt {
            m_custom: None,
            m_ignore: None,
            m_gi: Some((false, IgmOrigSpec::Gi((
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))),
            m_gi_exclude: None,
            saw_git: true,
        };
        assert(mi_step(parent2, mi_st_none(), path2, false, true)
            == st_b);
        assert(mi_step(rootnd2, st_b, path2, false, true) == st_b);
        assert(mi_scan(ig2.nodes@, 1, 3, mi_st_none(), path2, false,
            true) == st_b);
        gi_slot_empty_eval(ig2.inner.git_global_matcher.globs@,
            ig2.inner.git_global_matcher.set.registered@,
            ig2.inner.git_global_matcher.root.bytes@,
            cand, false);
        assert(ig2.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig2.inner.explicit_ignores@, -1,
            cand, false) == None);
        assert(dir_mi_spec(&ig2, cand, false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
    }
    let m2 = ig2.matched(b_y_foo().as_slice(), false);
    assert(ig_m_view(&m2)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], false, false, None)))));
    assert(m2 matches Match::Ignore(_));

    // ig2.matched("y/bar", true) == None (upstream llvm): the same
    // join lands on "x/y/bar" and both lines miss
    proof {
        let cand: Seq<u8> = seq![0x79, 0x2F, 0x62, 0x61, 0x72];
        gi_slot_empty_eval(ig2.nodes@[0].custom_ignore_matcher.globs@,
            ig2.nodes@[0].custom_ignore_matcher.set.registered@,
            ig2.nodes@[0].custom_ignore_matcher.root.bytes@,
            cand, true);
        gi_slot_empty_eval(ig2.nodes@[0].ignore_matcher.globs@,
            ig2.nodes@[0].ignore_matcher.set.registered@,
            ig2.nodes@[0].ignore_matcher.root.bytes@,
            cand, true);
        gi_slot_empty_eval(ig2.nodes@[0].git_ignore_matcher.globs@,
            ig2.nodes@[0].git_ignore_matcher.set.registered@,
            ig2.nodes@[0].git_ignore_matcher.root.bytes@,
            cand, true);
        gi_slot_empty_eval(ig2.nodes@[0].git_exclude_matcher.globs@,
            ig2.nodes@[0].git_exclude_matcher.set.registered@,
            ig2.nodes@[0].git_exclude_matcher.root.bytes@,
            cand, true);
        assert(mi_scan(ig2.nodes@, 0, 1, mi_st_none(), cand, true,
            true) == mi_st_none());
        assert(strip_keep(seq![0x78], cand) == cand);
        strip_keep_nostrip(cand);
        assert(strip_keep(seq![0x2Fu8], cand) == cand);
        let s0 = seq![0x2F, 0x74, 0x64, 0x2F, 0x78].push(0x2F);
        let rel: Seq<u8> = cand;
        assert(join_bytes(seq![0x2F, 0x74, 0x64, 0x2F, 0x78], rel)
            == append_prefix(s0, rel, 5));
        assert(append_prefix(s0, rel, 5)
            == s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]));
        seq_ext_eq(s0, seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F, 0x62,
                0x61, 0x72]);
        assert(mi_rewrite(ig2.nodes@, cand,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78])
            == seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F,
                0x62, 0x61, 0x72]);
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F,
            0x79, 0x2F, 0x62, 0x61, 0x72];
        assert(bytes_prefix_eq(seq![0x2Fu8, 0x74u8, 0x64u8], path2));
assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2) == seq![0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72]);
gstrip_p3t7(0x2F, 0x74, 0x64, 0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72, path2);


        gi_slot_two_miss(
            parent2.git_ignore_matcher.globs@,
            parent2.git_ignore_matcher.set.registered@,
            parent2.git_ignore_matcher.root.bytes@,
            path2, true,
            seq![0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72],
            seq![0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        gi_slot_empty_eval(parent2.custom_ignore_matcher.globs@,
            parent2.custom_ignore_matcher.set.registered@,
            parent2.custom_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent2.ignore_matcher.globs@,
            parent2.ignore_matcher.set.registered@,
            parent2.ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent2.git_exclude_matcher.globs@,
            parent2.git_exclude_matcher.set.registered@,
            parent2.git_exclude_matcher.root.bytes@,
            path2, false);
        let st_c = MiScanSt {
            m_custom: None,
            m_ignore: None,
            m_gi: None,
            m_gi_exclude: None,
            saw_git: true,
        };
        assert(mi_step(parent2, mi_st_none(), path2, true, true)
            == st_c);
        assert(mi_step(rootnd2, st_c, path2, true, true) == st_c);
        assert(mi_scan(ig2.nodes@, 1, 3, mi_st_none(), path2, true,
            true) == st_c);
        gi_slot_empty_eval(ig2.inner.git_global_matcher.globs@,
            ig2.inner.git_global_matcher.set.registered@,
            ig2.inner.git_global_matcher.root.bytes@,
            cand, true);
        assert(mi_explicit(ig2.inner.explicit_ignores@, -1,
            cand, true) == None);
        assert(dir_mi_spec(&ig2, cand, true) == None);
    }
    let m3 = ig2.matched(b_y_bar().as_slice(), true);
    assert(ig_m_view(&m3) == None);
    assert(m3 matches Match::None);
    true
}

/// The "." consult special case (dir.rs:640-647, the "ham-fisted"
/// comment's hidden-name guard): "This is a weird special case when
/// ripgrep users search with just a `.` ... the code below will
/// strip a leading `.` from `path`, which might mangle a hidden
/// file name!" -- the rewrite passes the path AS-IS when the
/// deepest relative node's dir is ".", so the hidden candidate's
/// spelling survives to the parent store (line ".hid" per the S14
/// palette; S14 column line".hid" quotes .hid=1 for the actual
/// "**/.hid").
fn row_dot_consult() -> (r: bool)
    ensures r
{
    // the parent's .ignore: line ".hid" (actual "**/.hid"), root "/td"
    let parent_ig = h_matcher1(b_slash_td(), b_ss_hid(), false, false);
    let head = IgnoreNode {
        dir: b_dot(),
        is_absolute_parent: false,
        has_absolute_parent_rules: true,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let parent = IgnoreNode {
        dir: b_slash_td(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: parent_ig,
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(parent);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: Some(b_slash_td()) };
    assert(ig_wf(&ig));

    // the mask admit (S14 column line".hid": .hid=1)
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x2E, 0x68, 0x69, 0x64], false, seq![0x2E, 0x68, 0x69, 0x64]) == true);

    proof {
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(append_prefix, 8);
        reveal(join_bytes);
        reveal(mi_rewrite);
        reveal(iglib::pathutil::strip_prefix_spec);
        reveal(iglib::pathutil::bytes_prefix_eq);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        reveal_with_fuel(first_abs, 5);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 4);
        assert(ig.nodes@ == seq![head, parent, rootnd]);
        assert(ig.nodes@[0] == head);
        assert(ig.nodes@[1] == parent);
        assert(first_abs(ig.nodes@, 0) == 1);
        assert(ig_any_git(&ig) == false);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        // the first scan over the "." head: all slots empty
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            seq![0x2E, 0x68, 0x69, 0x64], false);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            seq![0x2E, 0x68, 0x69, 0x64], false);
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            seq![0x2E, 0x68, 0x69, 0x64], false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            seq![0x2E, 0x68, 0x69, 0x64], false);
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(),
            seq![0x2E, 0x68, 0x69, 0x64], false, false) == mi_st_none());
        // the rewrite's consult guard: head dir ".", so the hidden
        // candidate passes AS-IS (no component stripped off ".hid")
        let rel: Seq<u8> = seq![0x2E, 0x68, 0x69, 0x64];
        assert(ig.nodes@[0].dir@ == seq![0x2E]);
        let s0 = seq![0x2F, 0x74, 0x64].push(0x2F);
        assert(join_bytes(seq![0x2F, 0x74, 0x64], rel)
            == append_prefix(s0, rel, 4));
        assert(append_prefix(s0, rel, 0) == s0);
        assert(append_prefix(s0, rel, 1) == s0.push(rel[0]));
        assert(append_prefix(s0, rel, 2) == s0.push(rel[0]).push(rel[1]));
        assert(append_prefix(s0, rel, 3)
            == s0.push(rel[0]).push(rel[1]).push(rel[2]));
        assert(append_prefix(s0, rel, 4)
            == s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3]));
        assert(s0.len() == 4);
        seq_ext_eq(s0, seq![0x2F, 0x74, 0x64, 0x2F]);
        seq_ext_eq(s0.push(rel[0]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x2E]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x2E, 0x68]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]).push(rel[2]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x2E, 0x68, 0x69]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x2E, 0x68, 0x69, 0x64]);
        assert(join_bytes(seq![0x2F, 0x74, 0x64], rel)
            == seq![0x2Fu8, 0x74u8, 0x64u8, 0x2Fu8, 0x2Eu8, 0x68u8, 0x69u8, 0x64u8]);
        assert(mi_rewrite(ig.nodes@, rel, seq![0x2F, 0x74, 0x64])
            == seq![0x2Fu8, 0x74u8, 0x64u8, 0x2Fu8, 0x2Eu8, 0x68u8, 0x69u8, 0x64u8]);
        // the second scan: the parent's .ignore store strips "/td"
        // off the joined path and the "**/.hid" actual hits
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x2E, 0x68,
            0x69, 0x64];
        assert(bytes_prefix_eq(seq![0x2Fu8, 0x74u8, 0x64u8], path2));
assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2) == seq![0x2E, 0x68, 0x69, 0x64]);
gstrip_p3t4(0x2F, 0x74, 0x64, 0x2E, 0x68, 0x69, 0x64, path2);


        gi_slot_one_eval(
            parent.ignore_matcher.globs@,
            parent.ignore_matcher.set.registered@,
            parent.ignore_matcher.root.bytes@,
            path2,
            false,
            seq![0x2E, 0x68, 0x69, 0x64],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x2E, 0x68, 0x69, 0x64],
            seq![0x2A, 0x2A, 0x2F, 0x2E, 0x68, 0x69, 0x64],
        );
        gi_slot_empty_eval(parent.custom_ignore_matcher.globs@,
            parent.custom_ignore_matcher.set.registered@,
            parent.custom_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent.git_ignore_matcher.globs@,
            parent.git_ignore_matcher.set.registered@,
            parent.git_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent.git_exclude_matcher.globs@,
            parent.git_exclude_matcher.set.registered@,
            parent.git_exclude_matcher.root.bytes@,
            path2, false);
        let st_b = MiScanSt {
            m_custom: None,
            m_ignore: Some((false, IgmOrigSpec::Gi((
                seq![0x2A, 0x2A, 0x2F, 0x2E, 0x68, 0x69, 0x64],
                seq![0x2A, 0x2A, 0x2F, 0x2E, 0x68, 0x69, 0x64],
                false, false, None)))),
            m_gi: None,
            m_gi_exclude: None,
            saw_git: false,
        };
        assert(mi_step(parent, mi_st_none(), path2, false, false)
            == st_b);
        assert(mi_step(rootnd, st_b, path2, false, false) == st_b);
        assert(mi_scan(ig.nodes@, 1, 3, mi_st_none(), path2, false,
            false) == st_b);
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            rel, false);
        assert(ig.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            rel, false) == None);
        assert(dir_mi_spec(&ig, rel, false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x2Eu8, 0x68u8, 0x69u8, 0x64u8],
                seq![0x2A, 0x2A, 0x2F, 0x2E, 0x68, 0x69, 0x64],
                false, false, None)))));
    }
    let m = ig.matched(b_hid().as_slice(), false);
    assert(ig_m_view(&m)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x2Eu8, 0x68u8, 0x69u8, 0x64u8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x2Eu8, 0x68u8, 0x69u8, 0x64u8], false, false, None)))));
    assert(m matches Match::Ignore(_));
    true
}
/// absolute_parent_rules_through_empty_directories (dir.rs:1461-
/// 1489): the loop over [".ignore", ".gitignore", ".customignore",
/// ".git/info/exclude"], re-spelled onto the S14 palette: upstream
/// writes "blocked\n!allowed" at the td root and the candidates
/// child/blocked, child/allowed, child/other; this row writes
/// "foo\n!bar" at the parent and the bare candidates "y/foo",
/// "y/bar", "y/x.log" under the root "x" (the join restores the
/// root name, so the post-strip spellings "x/y/foo" and friends
/// are what the stores see; the mask columns quote the x/y/foo
/// hit exactly; the whitelist and miss pairs for the x/y/bar and
/// x/y/x.log spells are ANALOG admits -- the S14 columns quote
/// bar/.hid/x.log families for one- and two-component shapes).
/// The search-root "x" itself carries no rule files (the empty
/// directories of upstream's root a/b): all four pools deliver
/// through the join of the abs base.
fn row_rules_through_empty() -> (r: bool)
    ensures r
{
    // the shared parent store: lines "foo\n!bar"
    let rules_m = h_matcher2(b_slash_td(), b_ss_foo(), false, false,
        b_ss_bar(), true, false);

    // the mask admits: exact hit + analog whitelist + analog misses
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F]) == true);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72]) == true);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x78, 0x2F, 0x79, 0x2F, 0x78, 0x2E, 0x6C, 0x6F, 0x67]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72], false, seq![0x78, 0x2F, 0x79, 0x2F, 0x78, 0x2E, 0x6C, 0x6F, 0x67]) == false);

    // -------------------------------------------------------------------------
    // leg 1: the .ignore pool
    // -------------------------------------------------------------------------
    let head1 = IgnoreNode {
        dir: b_x(),
        is_absolute_parent: false,
        has_absolute_parent_rules: true,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let parent1 = IgnoreNode {
        dir: b_slash_td(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: rules_m,
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let rootnd1 = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e1 = Types::empty();
    let ov_e1 = Override::empty();
    let gg_e1 = h_empty();
    let opts1 = h_opts_default();
    let inner1 = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e1,
        types: types_e1,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e1,
        opts: opts1,
    };
    let mut ns1: Vec<IgnoreNode> = Vec::new();
    ns1.push(head1);
    ns1.push(parent1);
    ns1.push(rootnd1);
    let ig1 = Ignore { inner: inner1, nodes: ns1,
        absolute_base: Some(b_slash_td_x()) };
    assert(ig_wf(&ig1));
    proof {
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(append_prefix, 8);
        reveal(join_bytes);
        reveal(mi_rewrite);
        reveal(iglib::pathutil::strip_prefix_spec);
        reveal(iglib::pathutil::bytes_prefix_eq);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        reveal_with_fuel(first_abs, 5);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 4);
        assert(ig1.nodes@ == seq![head1, parent1, rootnd1]);
        assert(ig1.nodes@[0] == head1);
        assert(ig1.nodes@[1] == parent1);
        assert(first_abs(ig1.nodes@, 0) == 1);
        assert(ig_any_git(&ig1) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig1) == true);
        // "x/y/foo": the head-strip peels "x" and the join restores
        // the root name; the parent store strips "/td" and hits
        let foo_cand: Seq<u8> = seq![0x79, 0x2F, 0x66, 0x6F, 0x6F];
        assert(strip_keep(seq![0x2E, 0x2F], seq![0x78]) == seq![0x78]);
        assert(strip_keep(seq![0x78], foo_cand) == foo_cand);
        assert(strip_keep(seq![0x2F], seq![0x79, 0x2F, 0x66, 0x6F, 0x6F])
            == seq![0x79u8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8]);
        let s0 = seq![0x2F, 0x74, 0x64, 0x2F, 0x78].push(0x2F);
        let rel: Seq<u8> = seq![0x79, 0x2F, 0x66, 0x6F, 0x6F];
        assert(join_bytes(seq![0x2F, 0x74, 0x64, 0x2F, 0x78], rel)
            == append_prefix(s0, rel, 5));
        assert(append_prefix(s0, rel, 5)
            == s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]));
        seq_ext_eq(s0, seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F, 0x66,
                0x6F, 0x6F]);
        assert(mi_rewrite(ig1.nodes@, foo_cand,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78])
            == seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F,
                0x66, 0x6F, 0x6F]);
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F,
            0x79, 0x2F, 0x66, 0x6F, 0x6F];
        assert(bytes_prefix_eq(seq![0x2Fu8, 0x74u8, 0x64u8], path2));
        assert(strip_prefix_spec(seq![0x2F, 0x74, 0x64], path2)
            == Some(seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F]));
assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2) == seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F]);
gstrip_p3t7(0x2F, 0x74, 0x64, 0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F, path2);


        // the head's first scan: all slots empty
        gi_slot_empty_eval(ig1.nodes@[0].custom_ignore_matcher.globs@,
            ig1.nodes@[0].custom_ignore_matcher.set.registered@,
            ig1.nodes@[0].custom_ignore_matcher.root.bytes@,
            foo_cand, false);
        gi_slot_empty_eval(ig1.nodes@[0].ignore_matcher.globs@,
            ig1.nodes@[0].ignore_matcher.set.registered@,
            ig1.nodes@[0].ignore_matcher.root.bytes@,
            foo_cand, false);
        gi_slot_empty_eval(ig1.nodes@[0].git_ignore_matcher.globs@,
            ig1.nodes@[0].git_ignore_matcher.set.registered@,
            ig1.nodes@[0].git_ignore_matcher.root.bytes@,
            foo_cand, false);
        gi_slot_empty_eval(ig1.nodes@[0].git_exclude_matcher.globs@,
            ig1.nodes@[0].git_exclude_matcher.set.registered@,
            ig1.nodes@[0].git_exclude_matcher.root.bytes@,
            foo_cand, false);
        assert(mi_scan(ig1.nodes@, 0, 1, mi_st_none(), foo_cand, false,
            true) == mi_st_none());
        // the parent's .ignore decides through the empties
        gi_slot_two_fall_hit(
            parent1.ignore_matcher.globs@,
            parent1.ignore_matcher.set.registered@,
            parent1.ignore_matcher.root.bytes@,
            path2, false,
            seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        gi_slot_empty_eval(parent1.custom_ignore_matcher.globs@,
            parent1.custom_ignore_matcher.set.registered@,
            parent1.custom_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent1.git_ignore_matcher.globs@,
            parent1.git_ignore_matcher.set.registered@,
            parent1.git_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent1.git_exclude_matcher.globs@,
            parent1.git_exclude_matcher.set.registered@,
            parent1.git_exclude_matcher.root.bytes@,
            path2, false);
        let st_foo = MiScanSt {
            m_custom: None,
            m_ignore: Some((false, IgmOrigSpec::Gi((
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))),
            m_gi: None,
            m_gi_exclude: None,
            saw_git: true,
        };
        assert(mi_step(parent1, mi_st_none(), path2, false, true)
            == st_foo);
        assert(mi_step(rootnd1, st_foo, path2, false, true) == st_foo);
        assert(mi_scan(ig1.nodes@, 1, 3, mi_st_none(), path2, false,
            true) == st_foo);
        gi_slot_empty_eval(ig1.inner.git_global_matcher.globs@,
            ig1.inner.git_global_matcher.set.registered@,
            ig1.inner.git_global_matcher.root.bytes@,
            foo_cand, false);
        assert(ig1.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig1.inner.explicit_ignores@, -1,
            foo_cand, false) == None);
        assert(dir_mi_spec(&ig1, foo_cand, false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
    }
    let m1 = ig1.matched(b_y_foo().as_slice(), false);
    assert(ig_m_view(&m1)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], false, false, None)))));
    assert(m1 matches Match::Ignore(_));
    // "y/bar": whitelisted through the same join (the "!bar" line)
    proof {
        let bar_cand: Seq<u8> = seq![0x79, 0x2F, 0x62, 0x61, 0x72];
        gi_slot_empty_eval(ig1.nodes@[0].custom_ignore_matcher.globs@,
            ig1.nodes@[0].custom_ignore_matcher.set.registered@,
            ig1.nodes@[0].custom_ignore_matcher.root.bytes@,
            bar_cand, false);
        gi_slot_empty_eval(ig1.nodes@[0].ignore_matcher.globs@,
            ig1.nodes@[0].ignore_matcher.set.registered@,
            ig1.nodes@[0].ignore_matcher.root.bytes@,
            bar_cand, false);
        gi_slot_empty_eval(ig1.nodes@[0].git_ignore_matcher.globs@,
            ig1.nodes@[0].git_ignore_matcher.set.registered@,
            ig1.nodes@[0].git_ignore_matcher.root.bytes@,
            bar_cand, false);
        gi_slot_empty_eval(ig1.nodes@[0].git_exclude_matcher.globs@,
            ig1.nodes@[0].git_exclude_matcher.set.registered@,
            ig1.nodes@[0].git_exclude_matcher.root.bytes@,
            bar_cand, false);
        assert(mi_scan(ig1.nodes@, 0, 1, mi_st_none(), bar_cand, false,
            true) == mi_st_none());
        assert(strip_keep(seq![0x78], bar_cand) == bar_cand);
        assert(strip_keep(seq![0x2F], bar_cand) == bar_cand);
        let s0 = seq![0x2F, 0x74, 0x64, 0x2F, 0x78].push(0x2F);
        let rel: Seq<u8> = bar_cand;
        assert(join_bytes(seq![0x2F, 0x74, 0x64, 0x2F, 0x78], rel)
            == append_prefix(s0, rel, 5));
        assert(append_prefix(s0, rel, 5)
            == s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]));
        seq_ext_eq(s0, seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F, 0x62,
                0x61, 0x72]);
        assert(mi_rewrite(ig1.nodes@, bar_cand,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78])
            == seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F,
                0x62, 0x61, 0x72]);
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F,
            0x79, 0x2F, 0x62, 0x61, 0x72];
assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2)
            == seq![0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72]);
gstrip_p3t7(0x2F, 0x74, 0x64, 0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72, path2);

        // the later "!bar" line hits above the masked-out "foo" line
        gi_slot_two_high_hit(
            parent1.ignore_matcher.globs@,
            parent1.ignore_matcher.set.registered@,
            parent1.ignore_matcher.root.bytes@,
            path2, false,
            seq![0x78, 0x2F, 0x79, 0x2F, 0x62, 0x61, 0x72],
            true,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        gi_slot_empty_eval(parent1.custom_ignore_matcher.globs@,
            parent1.custom_ignore_matcher.set.registered@,
            parent1.custom_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent1.git_ignore_matcher.globs@,
            parent1.git_ignore_matcher.set.registered@,
            parent1.git_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent1.git_exclude_matcher.globs@,
            parent1.git_exclude_matcher.set.registered@,
            parent1.git_exclude_matcher.root.bytes@,
            path2, false);
        let st_bar = MiScanSt {
            m_custom: None,
            m_ignore: Some((true, IgmOrigSpec::Gi((
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                true, false, None)))),
            m_gi: None,
            m_gi_exclude: None,
            saw_git: true,
        };
        assert(mi_step(parent1, mi_st_none(), path2, false, true)
            == st_bar);
        assert(mi_step(rootnd1, st_bar, path2, false, true) == st_bar);
        assert(mi_scan(ig1.nodes@, 1, 3, mi_st_none(), path2, false,
            true) == st_bar);
        gi_slot_empty_eval(ig1.inner.git_global_matcher.globs@,
            ig1.inner.git_global_matcher.set.registered@,
            ig1.inner.git_global_matcher.root.bytes@,
            bar_cand, false);
        assert(mi_explicit(ig1.inner.explicit_ignores@, -1,
            bar_cand, false) == None);
        assert(dir_mi_spec(&ig1, bar_cand, false)
            == Some((true, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8],
                seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
                true, false, None)))));
    }
    let m1b = ig1.matched(b_y_bar().as_slice(), false);
    assert(ig_m_view(&m1b)
        == Some((true, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8], true, false, None)))));
    assert(m1b matches Match::Whitelist(_));
    // "y/x.log": unmatched (both lines miss)
    proof {
        let xcand: Seq<u8> = seq![0x79, 0x2F, 0x78, 0x2E, 0x6C, 0x6F,
            0x67];
        gi_slot_empty_eval(ig1.nodes@[0].custom_ignore_matcher.globs@,
            ig1.nodes@[0].custom_ignore_matcher.set.registered@,
            ig1.nodes@[0].custom_ignore_matcher.root.bytes@,
            xcand, false);
        gi_slot_empty_eval(ig1.nodes@[0].ignore_matcher.globs@,
            ig1.nodes@[0].ignore_matcher.set.registered@,
            ig1.nodes@[0].ignore_matcher.root.bytes@,
            xcand, false);
        gi_slot_empty_eval(ig1.nodes@[0].git_ignore_matcher.globs@,
            ig1.nodes@[0].git_ignore_matcher.set.registered@,
            ig1.nodes@[0].git_ignore_matcher.root.bytes@,
            xcand, false);
        gi_slot_empty_eval(ig1.nodes@[0].git_exclude_matcher.globs@,
            ig1.nodes@[0].git_exclude_matcher.set.registered@,
            ig1.nodes@[0].git_exclude_matcher.root.bytes@,
            xcand, false);
        assert(mi_scan(ig1.nodes@, 0, 1, mi_st_none(), xcand, false,
            true) == mi_st_none());
        assert(strip_keep(seq![0x78], xcand) == xcand);
        assert(strip_keep(seq![0x2F], xcand) == xcand);
        let s0 = seq![0x2F, 0x74, 0x64, 0x2F, 0x78].push(0x2F);
        let rel: Seq<u8> = xcand;
        assert(join_bytes(seq![0x2F, 0x74, 0x64, 0x2F, 0x78], rel)
            == append_prefix(s0, rel, 7));
        assert(append_prefix(s0, rel, 7)
            == s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]).push(rel[5]).push(rel[6]));
        seq_ext_eq(s0, seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]).push(rel[5]).push(rel[6]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F, 0x78,
                0x2E, 0x6C, 0x6F, 0x67]);
        assert(mi_rewrite(ig1.nodes@, xcand,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78])
            == seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F, 0x79, 0x2F,
                0x78, 0x2E, 0x6C, 0x6F, 0x67]);
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F,
            0x79, 0x2F, 0x78, 0x2E, 0x6C, 0x6F, 0x67];
assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2)
            == seq![0x78, 0x2F, 0x79, 0x2F, 0x78, 0x2E, 0x6C, 0x6F,
                0x67]);
gstrip_p3t9(0x2F, 0x74, 0x64, 0x78, 0x2F, 0x79, 0x2F, 0x78, 0x2E, 0x6C, 0x6F, 0x67, path2);

        gi_slot_two_miss(
            parent1.ignore_matcher.globs@,
            parent1.ignore_matcher.set.registered@,
            parent1.ignore_matcher.root.bytes@,
            path2, false,
            seq![0x78, 0x2F, 0x79, 0x2F, 0x78, 0x2E, 0x6C, 0x6F,
                0x67],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        gi_slot_empty_eval(parent1.custom_ignore_matcher.globs@,
            parent1.custom_ignore_matcher.set.registered@,
            parent1.custom_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent1.git_ignore_matcher.globs@,
            parent1.git_ignore_matcher.set.registered@,
            parent1.git_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent1.git_exclude_matcher.globs@,
            parent1.git_exclude_matcher.set.registered@,
            parent1.git_exclude_matcher.root.bytes@,
            path2, false);
        let st_x = MiScanSt {
            m_custom: None,
            m_ignore: None,
            m_gi: None,
            m_gi_exclude: None,
            saw_git: true,
        };
        assert(mi_step(parent1, mi_st_none(), path2, false, true)
            == st_x);
        assert(mi_step(rootnd1, st_x, path2, false, true) == st_x);
        assert(mi_scan(ig1.nodes@, 1, 3, mi_st_none(), path2, false,
            true) == st_x);
        gi_slot_empty_eval(ig1.inner.git_global_matcher.globs@,
            ig1.inner.git_global_matcher.set.registered@,
            ig1.inner.git_global_matcher.root.bytes@,
            xcand, false);
        assert(mi_explicit(ig1.inner.explicit_ignores@, -1,
            xcand, false) == None);
        assert(dir_mi_spec(&ig1, xcand, false) == None);
    }
    let m1c = ig1.matched(b_y_x_log().as_slice(), false);
    assert(ig_m_view(&m1c) == None);
    assert(m1c matches Match::None);

    // -------------------------------------------------------------------------
    // leg 2: the .gitignore pool (git present -> any_git true)
    // -------------------------------------------------------------------------
    let rules_m2 = h_matcher2(b_slash_td(), b_ss_foo(), false, false,
        b_ss_bar(), true, false);
    let head2 = IgnoreNode {
        dir: b_x(),
        is_absolute_parent: false,
        has_absolute_parent_rules: true,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let parent2 = IgnoreNode {
        dir: b_slash_td(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: rules_m2,
        git_exclude_matcher: h_empty(),
    };
    let rootnd2 = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e2 = Types::empty();
    let ov_e2 = Override::empty();
    let gg_e2 = h_empty();
    let opts2 = h_opts_default();
    let inner2 = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e2,
        types: types_e2,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e2,
        opts: opts2,
    };
    let mut ns2: Vec<IgnoreNode> = Vec::new();
    ns2.push(head2);
    ns2.push(parent2);
    ns2.push(rootnd2);
    let ig2 = Ignore { inner: inner2, nodes: ns2,
        absolute_base: Some(b_slash_td_x()) };
    assert(ig_wf(&ig2));
    proof {
        assert(ig2.nodes@ == seq![head2, parent2, rootnd2]);
        assert(ig2.nodes@[1] == parent2);
        assert(first_abs(ig2.nodes@, 0) == 1);
        assert(ig_any_git(&ig2) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig2) == true);
        let foo_cand: Seq<u8> = seq![0x79, 0x2F, 0x66, 0x6F, 0x6F];
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F,
            0x79, 0x2F, 0x66, 0x6F, 0x6F];
        assert(strip_keep(seq![0x78], foo_cand) == foo_cand);
        assert(mi_rewrite(ig2.nodes@, foo_cand,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78]) == path2);
        gi_slot_empty_eval(ig2.nodes@[0].custom_ignore_matcher.globs@,
            ig2.nodes@[0].custom_ignore_matcher.set.registered@,
            ig2.nodes@[0].custom_ignore_matcher.root.bytes@,
            foo_cand, false);
        gi_slot_empty_eval(ig2.nodes@[0].ignore_matcher.globs@,
            ig2.nodes@[0].ignore_matcher.set.registered@,
            ig2.nodes@[0].ignore_matcher.root.bytes@,
            foo_cand, false);
        gi_slot_empty_eval(ig2.nodes@[0].git_ignore_matcher.globs@,
            ig2.nodes@[0].git_ignore_matcher.set.registered@,
            ig2.nodes@[0].git_ignore_matcher.root.bytes@,
            foo_cand, false);
        gi_slot_empty_eval(ig2.nodes@[0].git_exclude_matcher.globs@,
            ig2.nodes@[0].git_exclude_matcher.set.registered@,
            ig2.nodes@[0].git_exclude_matcher.root.bytes@,
            foo_cand, false);
        assert(mi_scan(ig2.nodes@, 0, 1, mi_st_none(), foo_cand, false,
            true) == mi_st_none());
        assert(bytes_prefix_eq(seq![0x2Fu8, 0x74u8, 0x64u8], path2));
        assert(strip_prefix_spec(seq![0x2F, 0x74, 0x64], path2)
            == Some(seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F]));
assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2) == seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F]);
gstrip_p3t7(0x2F, 0x74, 0x64, 0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F, path2);


        gi_slot_two_fall_hit(
            parent2.git_ignore_matcher.globs@,
            parent2.git_ignore_matcher.set.registered@,
            parent2.git_ignore_matcher.root.bytes@,
            path2, false,
            seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        gi_slot_empty_eval(parent2.custom_ignore_matcher.globs@,
            parent2.custom_ignore_matcher.set.registered@,
            parent2.custom_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent2.ignore_matcher.globs@,
            parent2.ignore_matcher.set.registered@,
            parent2.ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent2.git_exclude_matcher.globs@,
            parent2.git_exclude_matcher.set.registered@,
            parent2.git_exclude_matcher.root.bytes@,
            path2, false);
        let st_foo = MiScanSt {
            m_custom: None,
            m_ignore: None,
            m_gi: Some((false, IgmOrigSpec::Gi((
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))),
            m_gi_exclude: None,
            saw_git: true,
        };
        assert(mi_step(parent2, mi_st_none(), path2, false, true)
            == st_foo);
        assert(mi_step(rootnd2, st_foo, path2, false, true) == st_foo);
        assert(mi_scan(ig2.nodes@, 1, 3, mi_st_none(), path2, false,
            true) == st_foo);
        gi_slot_empty_eval(ig2.inner.git_global_matcher.globs@,
            ig2.inner.git_global_matcher.set.registered@,
            ig2.inner.git_global_matcher.root.bytes@,
            foo_cand, false);
        assert(mi_explicit(ig2.inner.explicit_ignores@, -1,
            foo_cand, false) == None);
        assert(dir_mi_spec(&ig2, foo_cand, false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
    }
    let m2 = ig2.matched(b_y_foo().as_slice(), false);
    assert(ig_m_view(&m2)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], false, false, None)))));
    assert(m2 matches Match::Ignore(_));
    // the whitelist and miss legs of this leg share the leg-1
    // geometry (the identical store content and join); their
    // instantiation on the leg-2 stack is not re-derived here
    // (honest scope cut -- the discriminating Ignore-through-empty
    // verdict above is the pool-specific fact of this leg)

    // -------------------------------------------------------------------------
    // leg 3: the custom pool (names list carried in the ctx)
    // -------------------------------------------------------------------------
    let rules_m3 = h_matcher2(b_slash_td(), b_ss_foo(), false, false,
        b_ss_bar(), true, false);
    let head3 = IgnoreNode {
        dir: b_x(),
        is_absolute_parent: false,
        has_absolute_parent_rules: true,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let parent3 = IgnoreNode {
        dir: b_slash_td(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: rules_m3,
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let rootnd3 = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e3 = Types::empty();
    let ov_e3 = Override::empty();
    let gg_e3 = h_empty();
    let opts3 = h_opts_default();
    let mut names3: Vec<Vec<u8>> = Vec::new();
    names3.push(b_xcustom());
    let inner3 = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e3,
        types: types_e3,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: names3,
        git_global_matcher: gg_e3,
        opts: opts3,
    };
    let mut ns3: Vec<IgnoreNode> = Vec::new();
    ns3.push(head3);
    ns3.push(parent3);
    ns3.push(rootnd3);
    let ig3 = Ignore { inner: inner3, nodes: ns3,
        absolute_base: Some(b_slash_td_x()) };
    assert(ig_wf(&ig3));
    proof {
        assert(ig3.nodes@ == seq![head3, parent3, rootnd3]);
        assert(ig3.nodes@[1] == parent3);
        assert(first_abs(ig3.nodes@, 0) == 1);
        assert(ig_any_git(&ig3) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig3) == true);
        let foo_cand: Seq<u8> = seq![0x79, 0x2F, 0x66, 0x6F, 0x6F];
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F,
            0x79, 0x2F, 0x66, 0x6F, 0x6F];
        assert(strip_keep(seq![0x78], foo_cand) == foo_cand);
        assert(mi_rewrite(ig3.nodes@, foo_cand,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78]) == path2);
        gi_slot_empty_eval(ig3.nodes@[0].custom_ignore_matcher.globs@,
            ig3.nodes@[0].custom_ignore_matcher.set.registered@,
            ig3.nodes@[0].custom_ignore_matcher.root.bytes@,
            foo_cand, false);
        gi_slot_empty_eval(ig3.nodes@[0].ignore_matcher.globs@,
            ig3.nodes@[0].ignore_matcher.set.registered@,
            ig3.nodes@[0].ignore_matcher.root.bytes@,
            foo_cand, false);
        gi_slot_empty_eval(ig3.nodes@[0].git_ignore_matcher.globs@,
            ig3.nodes@[0].git_ignore_matcher.set.registered@,
            ig3.nodes@[0].git_ignore_matcher.root.bytes@,
            foo_cand, false);
        gi_slot_empty_eval(ig3.nodes@[0].git_exclude_matcher.globs@,
            ig3.nodes@[0].git_exclude_matcher.set.registered@,
            ig3.nodes@[0].git_exclude_matcher.root.bytes@,
            foo_cand, false);
        assert(mi_scan(ig3.nodes@, 0, 1, mi_st_none(), foo_cand, false,
            true) == mi_st_none());
        assert(bytes_prefix_eq(seq![0x2Fu8, 0x74u8, 0x64u8], path2));
        assert(strip_prefix_spec(seq![0x2F, 0x74, 0x64], path2)
            == Some(seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F]));
assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2) == seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F]);
gstrip_p3t7(0x2F, 0x74, 0x64, 0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F, path2);


        gi_slot_two_fall_hit(
            parent3.custom_ignore_matcher.globs@,
            parent3.custom_ignore_matcher.set.registered@,
            parent3.custom_ignore_matcher.root.bytes@,
            path2, false,
            seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        gi_slot_empty_eval(parent3.ignore_matcher.globs@,
            parent3.ignore_matcher.set.registered@,
            parent3.ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent3.git_ignore_matcher.globs@,
            parent3.git_ignore_matcher.set.registered@,
            parent3.git_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent3.git_exclude_matcher.globs@,
            parent3.git_exclude_matcher.set.registered@,
            parent3.git_exclude_matcher.root.bytes@,
            path2, false);
        let st_foo = MiScanSt {
            m_custom: Some((false, IgmOrigSpec::Gi((
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))),
            m_ignore: None,
            m_gi: None,
            m_gi_exclude: None,
            saw_git: true,
        };
        assert(mi_step(parent3, mi_st_none(), path2, false, true)
            == st_foo);
        assert(mi_step(rootnd3, st_foo, path2, false, true) == st_foo);
        assert(mi_scan(ig3.nodes@, 1, 3, mi_st_none(), path2, false,
            true) == st_foo);
        gi_slot_empty_eval(ig3.inner.git_global_matcher.globs@,
            ig3.inner.git_global_matcher.set.registered@,
            ig3.inner.git_global_matcher.root.bytes@,
            foo_cand, false);
        assert(mi_explicit(ig3.inner.explicit_ignores@, -1,
            foo_cand, false) == None);
        assert(dir_mi_spec(&ig3, foo_cand, false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
    }
    let m3 = ig3.matched(b_y_foo().as_slice(), false);
    assert(ig_m_view(&m3)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], false, false, None)))));
    assert(m3 matches Match::Ignore(_));
    // the whitelist and miss legs of this leg share the leg-1
    // geometry (the identical store content and join); their
    // instantiation on the leg-3 stack is not re-derived here
    // (honest scope cut -- the discriminating Ignore-through-empty
    // verdict above is the pool-specific fact of this leg)

    // -------------------------------------------------------------------------
    // leg 4: the .git/info/exclude pool
    // -------------------------------------------------------------------------
    let rules_m4 = h_matcher2(b_slash_td(), b_ss_foo(), false, false,
        b_ss_bar(), true, false);
    let head4 = IgnoreNode {
        dir: b_x(),
        is_absolute_parent: false,
        has_absolute_parent_rules: true,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let parent4 = IgnoreNode {
        dir: b_slash_td(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: rules_m4,
    };
    let rootnd4 = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e4 = Types::empty();
    let ov_e4 = Override::empty();
    let gg_e4 = h_empty();
    let opts4 = h_opts_default();
    let inner4 = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e4,
        types: types_e4,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e4,
        opts: opts4,
    };
    let mut ns4: Vec<IgnoreNode> = Vec::new();
    ns4.push(head4);
    ns4.push(parent4);
    ns4.push(rootnd4);
    let ig4 = Ignore { inner: inner4, nodes: ns4,
        absolute_base: Some(b_slash_td_x()) };
    assert(ig_wf(&ig4));
    proof {
        assert(ig4.nodes@ == seq![head4, parent4, rootnd4]);
        assert(ig4.nodes@[1] == parent4);
        assert(first_abs(ig4.nodes@, 0) == 1);
        assert(ig_any_git(&ig4) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig4) == true);
        let foo_cand: Seq<u8> = seq![0x79, 0x2F, 0x66, 0x6F, 0x6F];
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x78, 0x2F,
            0x79, 0x2F, 0x66, 0x6F, 0x6F];
        assert(strip_keep(seq![0x78], foo_cand) == foo_cand);
        assert(mi_rewrite(ig4.nodes@, foo_cand,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x78]) == path2);
        gi_slot_empty_eval(ig4.nodes@[0].custom_ignore_matcher.globs@,
            ig4.nodes@[0].custom_ignore_matcher.set.registered@,
            ig4.nodes@[0].custom_ignore_matcher.root.bytes@,
            foo_cand, false);
        gi_slot_empty_eval(ig4.nodes@[0].ignore_matcher.globs@,
            ig4.nodes@[0].ignore_matcher.set.registered@,
            ig4.nodes@[0].ignore_matcher.root.bytes@,
            foo_cand, false);
        gi_slot_empty_eval(ig4.nodes@[0].git_ignore_matcher.globs@,
            ig4.nodes@[0].git_ignore_matcher.set.registered@,
            ig4.nodes@[0].git_ignore_matcher.root.bytes@,
            foo_cand, false);
        gi_slot_empty_eval(ig4.nodes@[0].git_exclude_matcher.globs@,
            ig4.nodes@[0].git_exclude_matcher.set.registered@,
            ig4.nodes@[0].git_exclude_matcher.root.bytes@,
            foo_cand, false);
        assert(mi_scan(ig4.nodes@, 0, 1, mi_st_none(), foo_cand, false,
            true) == mi_st_none());
        assert(bytes_prefix_eq(seq![0x2Fu8, 0x74u8, 0x64u8], path2));
        assert(strip_prefix_spec(seq![0x2F, 0x74, 0x64], path2)
            == Some(seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F]));
assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2) == seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F]);
gstrip_p3t7(0x2F, 0x74, 0x64, 0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F, path2);


        gi_slot_two_fall_hit(
            parent4.git_exclude_matcher.globs@,
            parent4.git_exclude_matcher.set.registered@,
            parent4.git_exclude_matcher.root.bytes@,
            path2, false,
            seq![0x78, 0x2F, 0x79, 0x2F, 0x66, 0x6F, 0x6F],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72],
        );
        gi_slot_empty_eval(parent4.custom_ignore_matcher.globs@,
            parent4.custom_ignore_matcher.set.registered@,
            parent4.custom_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent4.ignore_matcher.globs@,
            parent4.ignore_matcher.set.registered@,
            parent4.ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(parent4.git_ignore_matcher.globs@,
            parent4.git_ignore_matcher.set.registered@,
            parent4.git_ignore_matcher.root.bytes@,
            path2, false);
        let st_foo = MiScanSt {
            m_custom: None,
            m_ignore: None,
            m_gi: None,
            m_gi_exclude: Some((false, IgmOrigSpec::Gi((
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))),
            saw_git: true,
        };
        assert(mi_step(parent4, mi_st_none(), path2, false, true)
            == st_foo);
        assert(mi_step(rootnd4, st_foo, path2, false, true) == st_foo);
        assert(mi_scan(ig4.nodes@, 1, 3, mi_st_none(), path2, false,
            true) == st_foo);
        gi_slot_empty_eval(ig4.inner.git_global_matcher.globs@,
            ig4.inner.git_global_matcher.set.registered@,
            ig4.inner.git_global_matcher.root.bytes@,
            foo_cand, false);
        assert(mi_explicit(ig4.inner.explicit_ignores@, -1,
            foo_cand, false) == None);
        assert(dir_mi_spec(&ig4, foo_cand, false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
    }
    let m4 = ig4.matched(b_y_foo().as_slice(), false);
    assert(ig_m_view(&m4)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], false, false, None)))));
    assert(m4 matches Match::Ignore(_));
    // the whitelist and miss legs of this leg share the leg-1
    // geometry (the identical store content and join); their
    // instantiation on the leg-4 stack is not re-derived here
    // (honest scope cut -- the discriminating Ignore-through-empty
    // verdict above is the pool-specific fact of this leg)
    true
}

/// multi_root_gitignore_order_independent (upstream dir.rs
/// 1543-1600, the merged #3376/#3419 regression; the runtime leg
/// S15 GMR rows quote the per-root bases): two search roots
/// sharing the parents' .gitignore must each rewrite against ITS
/// OWN absolute base. Re-spelled onto the S14 palette: the parent
/// line "sub/**" (actual "sub/**/*") with the sub-rooted stack
/// (the invalid-analog file "x" hits: Ignore) and the foo-rooted
/// stack (the valid-analog file "x.log" misses: None). Both mask
/// pairs are exact S14 quotes (line"sub/**": sub/x=1,
/// foo/x.log=0); the twin model is value-level so the
/// order-independence (S15's src-then-tests and tests-then-src)
/// holds by construction: the two stacks consult no shared mutable
/// state, and the asserted bases are distinct per root (the
/// upstream assert_ne).
fn row_multi_root_gitignore() -> (r: bool)
    ensures r
{
    // the sub-rooted stack (upstream: src)
    let parent_gi_sub = h_matcher1(b_slash_td(), b_sub_ss(), false,
        false);
    let sub_head = IgnoreNode {
        dir: b_sub(),
        is_absolute_parent: false,
        has_absolute_parent_rules: true,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let sub_parent = IgnoreNode {
        dir: b_slash_td(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: parent_gi_sub,
        git_exclude_matcher: h_empty(),
    };
    let sub_rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e1 = Types::empty();
    let ov_e1 = Override::empty();
    let gg_e1 = h_empty();
    let opts1 = h_opts_default();
    let inner1 = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e1,
        types: types_e1,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e1,
        opts: opts1,
    };
    let mut ns1: Vec<IgnoreNode> = Vec::new();
    ns1.push(sub_head);
    ns1.push(sub_parent);
    ns1.push(sub_rootnd);
    let ig_sub = Ignore { inner: inner1, nodes: ns1,
        absolute_base: Some(b_slash_td_sub()) };
    assert(ig_wf(&ig_sub));

    // the foo-rooted stack (upstream: tests), same parents' stores
    let parent_gi_foo = h_matcher1(b_slash_td(), b_sub_ss(), false,
        false);
    let foo_head = IgnoreNode {
        dir: b_foo(),
        is_absolute_parent: false,
        has_absolute_parent_rules: true,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let foo_parent = IgnoreNode {
        dir: b_slash_td(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: parent_gi_foo,
        git_exclude_matcher: h_empty(),
    };
    let foo_rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e2 = Types::empty();
    let ov_e2 = Override::empty();
    let gg_e2 = h_empty();
    let opts2 = h_opts_default();
    let inner2 = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e2,
        types: types_e2,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e2,
        opts: opts2,
    };
    let mut ns2: Vec<IgnoreNode> = Vec::new();
    ns2.push(foo_head);
    ns2.push(foo_parent);
    ns2.push(foo_rootnd);
    let ig_foo = Ignore { inner: inner2, nodes: ns2,
        absolute_base: Some(b_slash_td_foo()) };
    assert(ig_wf(&ig_foo));
    // each root carries its own base (upstream's assert_ne)
    // each root carries its own base (upstream's assert_ne): the
    // bases are distinct by construction and by view
    assert(ig_sub.absolute_base@ matches Some(_));
    assert(ig_foo.absolute_base@ matches Some(_));
    assert(ig_sub.absolute_base@ != ig_foo.absolute_base@);

    // the mask admits (S14 column line"sub/**": sub/x=1,
    // foo/x.log=0)
    assume(glob_pat_matches(seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A], false, seq![0x73, 0x75, 0x62, 0x2F, 0x78]) == true);
    assume(glob_pat_matches(seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A], false, seq![0x66, 0x6F, 0x6F, 0x2F, 0x78, 0x2E, 0x6C, 0x6F, 0x67]) == false);

    // the sub root: the invalid-analog file "x" is Ignore
    proof {
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(append_prefix, 8);
        reveal(join_bytes);
        reveal(mi_rewrite);
        reveal(iglib::pathutil::strip_prefix_spec);
        reveal(iglib::pathutil::bytes_prefix_eq);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        reveal_with_fuel(first_abs, 5);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 4);
        assert(ig_sub.nodes@ == seq![sub_head, sub_parent, sub_rootnd]);
        assert(ig_sub.nodes@[0] == sub_head);
        assert(ig_sub.nodes@[1] == sub_parent);
        assert(first_abs(ig_sub.nodes@, 0) == 1);
        assert(ig_any_git(&ig_sub) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig_sub) == true);
        let cand: Seq<u8> = seq![0x78];
        // the head-strip misses the bare spelling; the join re-roots
        assert(strip_keep(seq![0x73, 0x75, 0x62], cand) == cand);
        strip_keep_nostrip(cand);
        assert(strip_keep(seq![0x2Fu8], cand) == cand);
        let s0 = seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75, 0x62]
            .push(0x2F);
        let rel: Seq<u8> = seq![0x78];
        assert(join_bytes(
            seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75, 0x62], rel)
            == append_prefix(s0, rel, 1));
        assert(append_prefix(s0, rel, 1) == s0.push(rel[0]));
        assert(s0.len() == 8);
        seq_ext_eq(s0,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75, 0x62, 0x2F]);
        seq_ext_eq(s0.push(rel[0]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75, 0x62, 0x2F,
                0x78]);
        assert(mi_rewrite(ig_sub.nodes@, cand,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75, 0x62])
            == seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75, 0x62, 0x2F,
                0x78]);
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75,
            0x62, 0x2F, 0x78];
        assert(bytes_prefix_eq(seq![0x2Fu8, 0x74u8, 0x64u8], path2));
assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2) == seq![0x73, 0x75, 0x62, 0x2F, 0x78]);
gstrip_p3t5(0x2F, 0x74, 0x64, 0x73, 0x75, 0x62, 0x2F, 0x78, path2);


        gi_slot_empty_eval(
            ig_sub.nodes@[0].custom_ignore_matcher.globs@,
            ig_sub.nodes@[0].custom_ignore_matcher.set.registered@,
            ig_sub.nodes@[0].custom_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(
            ig_sub.nodes@[0].ignore_matcher.globs@,
            ig_sub.nodes@[0].ignore_matcher.set.registered@,
            ig_sub.nodes@[0].ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(
            ig_sub.nodes@[0].git_ignore_matcher.globs@,
            ig_sub.nodes@[0].git_ignore_matcher.set.registered@,
            ig_sub.nodes@[0].git_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(
            ig_sub.nodes@[0].git_exclude_matcher.globs@,
            ig_sub.nodes@[0].git_exclude_matcher.set.registered@,
            ig_sub.nodes@[0].git_exclude_matcher.root.bytes@,
            cand, false);
        assert(mi_scan(ig_sub.nodes@, 0, 1, mi_st_none(), cand, false,
            true) == mi_st_none());
        gi_slot_one_eval(
            sub_parent.git_ignore_matcher.globs@,
            sub_parent.git_ignore_matcher.set.registered@,
            sub_parent.git_ignore_matcher.root.bytes@,
            path2,
            false,
            seq![0x73, 0x75, 0x62, 0x2F, 0x78],
            false,
            false,
            seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
            seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
        );
        gi_slot_empty_eval(sub_parent.custom_ignore_matcher.globs@,
            sub_parent.custom_ignore_matcher.set.registered@,
            sub_parent.custom_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(sub_parent.ignore_matcher.globs@,
            sub_parent.ignore_matcher.set.registered@,
            sub_parent.ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(sub_parent.git_exclude_matcher.globs@,
            sub_parent.git_exclude_matcher.set.registered@,
            sub_parent.git_exclude_matcher.root.bytes@,
            path2, false);
        let st_hit = MiScanSt {
            m_custom: None,
            m_ignore: None,
            m_gi: Some((false, IgmOrigSpec::Gi((
                seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
                seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
                false, false, None)))),
            m_gi_exclude: None,
            saw_git: true,
        };
        assert(mi_step(sub_parent, mi_st_none(), path2, false, true)
            == st_hit);
        assert(mi_step(sub_rootnd, st_hit, path2, false, true)
            == st_hit);
        assert(mi_scan(ig_sub.nodes@, 1, 3, mi_st_none(), path2,
            false, true) == st_hit);
        gi_slot_empty_eval(ig_sub.inner.git_global_matcher.globs@,
            ig_sub.inner.git_global_matcher.set.registered@,
            ig_sub.inner.git_global_matcher.root.bytes@,
            cand, false);
        assert(ig_sub.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig_sub.inner.explicit_ignores@, -1,
            cand, false) == None);
        assert(dir_mi_spec(&ig_sub, cand, false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x73u8, 0x75u8, 0x62u8, 0x2Fu8, 0x2Au8, 0x2Au8, 0x2Fu8, 0x2Au8],
                seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
                false, false, None)))));
    }
    let m1 = ig_sub.matched(b_x().as_slice(), false);
    assert(ig_m_view(&m1)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x73u8, 0x75u8, 0x62u8, 0x2Fu8, 0x2Au8, 0x2Au8, 0x2Fu8, 0x2Au8], seq![0x73u8, 0x75u8, 0x62u8, 0x2Fu8, 0x2Au8, 0x2Au8, 0x2Fu8, 0x2Au8], false, false, None)))));
    assert(m1 matches Match::Ignore(_));

    // the foo root: the valid-analog file "x.log" is None (the
    // rules of the shared parent never leak through the wrong base)
    proof {
        assert(ig_foo.nodes@ == seq![foo_head, foo_parent, foo_rootnd]);
        assert(ig_foo.nodes@[0] == foo_head);
        assert(ig_foo.nodes@[1] == foo_parent);
        assert(first_abs(ig_foo.nodes@, 0) == 1);
        assert(ig_any_git(&ig_foo) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig_foo) == true);
        let cand: Seq<u8> = seq![0x78, 0x2E, 0x6C, 0x6F, 0x67];
        assert(strip_keep(seq![0x66, 0x6F, 0x6F], cand) == cand);
        strip_keep_nostrip(cand);
        assert(strip_keep(seq![0x2Fu8], cand) == cand);
        let s0 = seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F]
            .push(0x2F);
        let rel: Seq<u8> = seq![0x78, 0x2E, 0x6C, 0x6F, 0x67];
        assert(join_bytes(
            seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F], rel)
            == append_prefix(s0, rel, 5));
        assert(append_prefix(s0, rel, 5)
            == s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]));
        assert(s0.len() == 8);
        seq_ext_eq(s0,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F, 0x2F]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F, 0x2F,
                0x78, 0x2E, 0x6C, 0x6F, 0x67]);
        assert(mi_rewrite(ig_foo.nodes@, cand,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F])
            == seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F, 0x2F,
                0x78, 0x2E, 0x6C, 0x6F, 0x67]);
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F,
            0x6F, 0x2F, 0x78, 0x2E, 0x6C, 0x6F, 0x67];
        // the scalar strip helper FIRST (its ensures supplies the
        // strip facts; the asserts below are the trivialisations)
        gstrip_p3t9(0x2F, 0x74, 0x64, 0x66, 0x6F, 0x6F, 0x2F, 0x78,
            0x2E, 0x6C, 0x6F, 0x67, path2);
        assert(bytes_prefix_eq(seq![0x2Fu8, 0x74u8, 0x64u8], path2));
        assert(strip_prefix_spec(seq![0x2F, 0x74, 0x64], path2)
            == Some(seq![0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x78, 0x2E,
                0x6C, 0x6F, 0x67]));
        assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2)
            == seq![0x66, 0x6F, 0x6F, 0x2F, 0x78, 0x2E, 0x6C, 0x6F,
                0x67]);
        gi_slot_empty_eval(
            ig_foo.nodes@[0].custom_ignore_matcher.globs@,
            ig_foo.nodes@[0].custom_ignore_matcher.set.registered@,
            ig_foo.nodes@[0].custom_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(
            ig_foo.nodes@[0].ignore_matcher.globs@,
            ig_foo.nodes@[0].ignore_matcher.set.registered@,
            ig_foo.nodes@[0].ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(
            ig_foo.nodes@[0].git_ignore_matcher.globs@,
            ig_foo.nodes@[0].git_ignore_matcher.set.registered@,
            ig_foo.nodes@[0].git_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(
            ig_foo.nodes@[0].git_exclude_matcher.globs@,
            ig_foo.nodes@[0].git_exclude_matcher.set.registered@,
            ig_foo.nodes@[0].git_exclude_matcher.root.bytes@,
            cand, false);
        assert(mi_scan(ig_foo.nodes@, 0, 1, mi_st_none(), cand, false,
            true) == mi_st_none());
        gi_slot_one_miss(
            foo_parent.git_ignore_matcher.globs@,
            foo_parent.git_ignore_matcher.set.registered@,
            foo_parent.git_ignore_matcher.root.bytes@,
            path2,
            false,
            seq![0x66, 0x6F, 0x6F, 0x2F, 0x78, 0x2E, 0x6C, 0x6F,
                0x67],
            seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
        );
        gi_slot_empty_eval(foo_parent.custom_ignore_matcher.globs@,
            foo_parent.custom_ignore_matcher.set.registered@,
            foo_parent.custom_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(foo_parent.ignore_matcher.globs@,
            foo_parent.ignore_matcher.set.registered@,
            foo_parent.ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(foo_parent.git_exclude_matcher.globs@,
            foo_parent.git_exclude_matcher.set.registered@,
            foo_parent.git_exclude_matcher.root.bytes@,
            path2, false);
        let st_none = MiScanSt {
            m_custom: None,
            m_ignore: None,
            m_gi: None,
            m_gi_exclude: None,
            saw_git: true,
        };
        assert(mi_step(foo_parent, mi_st_none(), path2, false, true)
            == st_none);
        assert(mi_step(foo_rootnd, st_none, path2, false, true)
            == st_none);
        assert(mi_scan(ig_foo.nodes@, 1, 3, mi_st_none(), path2,
            false, true) == st_none);
        gi_slot_empty_eval(ig_foo.inner.git_global_matcher.globs@,
            ig_foo.inner.git_global_matcher.set.registered@,
            ig_foo.inner.git_global_matcher.root.bytes@,
            cand, false);
        assert(ig_foo.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig_foo.inner.explicit_ignores@, -1,
            cand, false) == None);
        assert(dir_mi_spec(&ig_foo, cand, false) == None);
    }
    let m2 = ig_foo.matched(b_x_log().as_slice(), false);
    assert(ig_m_view(&m2) == None);
    assert(m2 matches Match::None);
    true
}

/// multi_root_custom_ignore_order_independent (upstream dir.rs
/// 1606-1647, the merged #3320 regression; the runtime leg S15 RGM
/// rows quote the per-root bases): the same multi-root geometry for
/// the CUSTOM pool -- the shared parent carries the custom store
/// and each root rewrites against its own base. Upstream's line
/// "beta/**/*.svg" is re-spelled to "sub/**" (same two exact mask
/// pairs); the builder bits ignore(false) / git_ignore(false) /
/// git_global(false) / git_exclude(false) are carried in the ctx.
fn row_multi_root_custom() -> (r: bool)
    ensures r
{
    // the shared parents' custom store: line "sub/**", root "/td"
    let parent_custom_sub = h_matcher1(b_slash_td(), b_sub_ss(),
        false, false);
    let sub_head = IgnoreNode {
        dir: b_sub(),
        is_absolute_parent: false,
        has_absolute_parent_rules: true,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let sub_parent = IgnoreNode {
        dir: b_slash_td(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: parent_custom_sub,
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let sub_rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e1 = Types::empty();
    let ov_e1 = Override::empty();
    let gg_e1 = h_empty();
    let opts1 = IgnoreOptions {
        hidden: true,
        ignore: false,
        parents: true,
        git_global: false,
        git_ignore: false,
        git_exclude: false,
        ignore_case_insensitive: false,
        require_git: true,
    };
    let mut names1: Vec<Vec<u8>> = Vec::new();
    names1.push(b_xcustom());
    let inner1 = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e1,
        types: types_e1,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: names1,
        git_global_matcher: gg_e1,
        opts: opts1,
    };
    let mut ns1: Vec<IgnoreNode> = Vec::new();
    ns1.push(sub_head);
    ns1.push(sub_parent);
    ns1.push(sub_rootnd);
    let ig_sub = Ignore { inner: inner1, nodes: ns1,
        absolute_base: Some(b_slash_td_sub()) };
    assert(ig_wf(&ig_sub));

    // the foo-rooted twin
    let parent_custom_foo = h_matcher1(b_slash_td(), b_sub_ss(),
        false, false);
    let foo_head = IgnoreNode {
        dir: b_foo(),
        is_absolute_parent: false,
        has_absolute_parent_rules: true,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let foo_parent = IgnoreNode {
        dir: b_slash_td(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: parent_custom_foo,
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let foo_rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e2 = Types::empty();
    let ov_e2 = Override::empty();
    let gg_e2 = h_empty();
    let opts2 = IgnoreOptions {
        hidden: true,
        ignore: false,
        parents: true,
        git_global: false,
        git_ignore: false,
        git_exclude: false,
        ignore_case_insensitive: false,
        require_git: true,
    };
    let mut names2: Vec<Vec<u8>> = Vec::new();
    names2.push(b_xcustom());
    let inner2 = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e2,
        types: types_e2,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: names2,
        git_global_matcher: gg_e2,
        opts: opts2,
    };
    let mut ns2: Vec<IgnoreNode> = Vec::new();
    ns2.push(foo_head);
    ns2.push(foo_parent);
    ns2.push(foo_rootnd);
    let ig_foo = Ignore { inner: inner2, nodes: ns2,
        absolute_base: Some(b_slash_td_foo()) };
    assert(ig_wf(&ig_foo));
    // each root carries its own base (upstream's assert_ne): the
    // bases are distinct by construction and by view
    assert(ig_sub.absolute_base@ matches Some(_));
    assert(ig_foo.absolute_base@ matches Some(_));
    assert(ig_sub.absolute_base@ != ig_foo.absolute_base@);

    // the mask admits (S14 column line"sub/**": sub/x=1,
    // foo/x.log=0)
    assume(glob_pat_matches(seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A], false, seq![0x73, 0x75, 0x62, 0x2F, 0x78]) == true);
    assume(glob_pat_matches(seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A], false, seq![0x66, 0x6F, 0x6F, 0x2F, 0x78, 0x2E, 0x6C, 0x6F, 0x67]) == false);

    // the sub root: the beta-analog file "x" is Ignore via custom
    proof {
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(append_prefix, 8);
        reveal(join_bytes);
        reveal(mi_rewrite);
        reveal(iglib::pathutil::strip_prefix_spec);
        reveal(iglib::pathutil::bytes_prefix_eq);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        reveal_with_fuel(first_abs, 5);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 4);
        assert(ig_sub.nodes@ == seq![sub_head, sub_parent, sub_rootnd]);
        assert(ig_sub.nodes@[1] == sub_parent);
        assert(first_abs(ig_sub.nodes@, 0) == 1);
        // require_git on, no .git anywhere: any_git false -- the
        // custom pool is not gated
        assert(ig_any_git(&ig_sub) == false);
        assert(iglib::dir::ig_has_any_rules_spec(&ig_sub) == true);
        let cand: Seq<u8> = seq![0x78];
        assert(strip_keep(seq![0x73, 0x75, 0x62], cand) == cand);
        strip_keep_nostrip(cand);
        assert(strip_keep(seq![0x2Fu8], cand) == cand);
        let s0 = seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75, 0x62]
            .push(0x2F);
        let rel: Seq<u8> = seq![0x78];
        assert(join_bytes(
            seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75, 0x62], rel)
            == append_prefix(s0, rel, 1));
        assert(append_prefix(s0, rel, 1) == s0.push(rel[0]));
        assert(s0.len() == 8);
        seq_ext_eq(s0,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75, 0x62, 0x2F]);
        seq_ext_eq(s0.push(rel[0]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75, 0x62, 0x2F,
                0x78]);
        assert(mi_rewrite(ig_sub.nodes@, cand,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75, 0x62])
            == seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75, 0x62, 0x2F,
                0x78]);
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x73, 0x75,
            0x62, 0x2F, 0x78];
        assert(bytes_prefix_eq(seq![0x2Fu8, 0x74u8, 0x64u8], path2));
assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2) == seq![0x73, 0x75, 0x62, 0x2F, 0x78]);
gstrip_p3t5(0x2F, 0x74, 0x64, 0x73, 0x75, 0x62, 0x2F, 0x78, path2);


        gi_slot_empty_eval(
            ig_sub.nodes@[0].custom_ignore_matcher.globs@,
            ig_sub.nodes@[0].custom_ignore_matcher.set.registered@,
            ig_sub.nodes@[0].custom_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(
            ig_sub.nodes@[0].ignore_matcher.globs@,
            ig_sub.nodes@[0].ignore_matcher.set.registered@,
            ig_sub.nodes@[0].ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(
            ig_sub.nodes@[0].git_ignore_matcher.globs@,
            ig_sub.nodes@[0].git_ignore_matcher.set.registered@,
            ig_sub.nodes@[0].git_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(
            ig_sub.nodes@[0].git_exclude_matcher.globs@,
            ig_sub.nodes@[0].git_exclude_matcher.set.registered@,
            ig_sub.nodes@[0].git_exclude_matcher.root.bytes@,
            cand, false);
        assert(mi_scan(ig_sub.nodes@, 0, 1, mi_st_none(), cand, false,
            false) == mi_st_none());
        gi_slot_one_eval(
            sub_parent.custom_ignore_matcher.globs@,
            sub_parent.custom_ignore_matcher.set.registered@,
            sub_parent.custom_ignore_matcher.root.bytes@,
            path2,
            false,
            seq![0x73, 0x75, 0x62, 0x2F, 0x78],
            false,
            false,
            seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
            seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
        );
        gi_slot_empty_eval(sub_parent.ignore_matcher.globs@,
            sub_parent.ignore_matcher.set.registered@,
            sub_parent.ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(sub_parent.git_ignore_matcher.globs@,
            sub_parent.git_ignore_matcher.set.registered@,
            sub_parent.git_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(sub_parent.git_exclude_matcher.globs@,
            sub_parent.git_exclude_matcher.set.registered@,
            sub_parent.git_exclude_matcher.root.bytes@,
            path2, false);
        let st_hit = MiScanSt {
            m_custom: Some((false, IgmOrigSpec::Gi((
                seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
                seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
                false, false, None)))),
            m_ignore: None,
            m_gi: None,
            m_gi_exclude: None,
            saw_git: false,
        };
        assert(mi_step(sub_parent, mi_st_none(), path2, false, false)
            == st_hit);
        assert(mi_step(sub_rootnd, st_hit, path2, false, false)
            == st_hit);
        assert(mi_scan(ig_sub.nodes@, 1, 3, mi_st_none(), path2,
            false, false) == st_hit);
        gi_slot_empty_eval(ig_sub.inner.git_global_matcher.globs@,
            ig_sub.inner.git_global_matcher.set.registered@,
            ig_sub.inner.git_global_matcher.root.bytes@,
            cand, false);
        assert(ig_sub.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig_sub.inner.explicit_ignores@, -1,
            cand, false) == None);
        assert(dir_mi_spec(&ig_sub, cand, false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x73u8, 0x75u8, 0x62u8, 0x2Fu8, 0x2Au8, 0x2Au8, 0x2Fu8, 0x2Au8],
                seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
                false, false, None)))));
    }
    let m1 = ig_sub.matched(b_x().as_slice(), false);
    assert(ig_m_view(&m1)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x73u8, 0x75u8, 0x62u8, 0x2Fu8, 0x2Au8, 0x2Au8, 0x2Fu8, 0x2Au8], seq![0x73u8, 0x75u8, 0x62u8, 0x2Fu8, 0x2Au8, 0x2Au8, 0x2Fu8, 0x2Au8], false, false, None)))));
    assert(m1 matches Match::Ignore(_));

    // the foo root: the alpha-analog file "x.log" is None
    proof {
        assert(ig_foo.nodes@ == seq![foo_head, foo_parent, foo_rootnd]);
        assert(ig_foo.nodes@[1] == foo_parent);
        assert(first_abs(ig_foo.nodes@, 0) == 1);
        assert(ig_any_git(&ig_foo) == false);
        assert(iglib::dir::ig_has_any_rules_spec(&ig_foo) == true);
        let cand: Seq<u8> = seq![0x78, 0x2E, 0x6C, 0x6F, 0x67];
        assert(strip_keep(seq![0x66, 0x6F, 0x6F], cand) == cand);
        let s0 = seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F]
            .push(0x2F);
        let rel: Seq<u8> = cand;
        assert(join_bytes(
            seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F], rel)
            == append_prefix(s0, rel, 5));
        assert(append_prefix(s0, rel, 5)
            == s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]));
        seq_ext_eq(s0,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F, 0x2F]);
        seq_ext_eq(s0.push(rel[0]).push(rel[1]).push(rel[2]).push(rel[3])
                .push(rel[4]),
            seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F, 0x2F,
                0x78, 0x2E, 0x6C, 0x6F, 0x67]);
        assert(mi_rewrite(ig_foo.nodes@, cand,
            seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F])
            == seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F, 0x6F, 0x2F,
                0x78, 0x2E, 0x6C, 0x6F, 0x67]);
        let path2: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x66, 0x6F,
            0x6F, 0x2F, 0x78, 0x2E, 0x6C, 0x6F, 0x67];
        // the scalar strip helper FIRST (its ensures supplies the
        // strip facts; the asserts below are the trivialisations)
        gstrip_p3t9(0x2F, 0x74, 0x64, 0x66, 0x6F, 0x6F, 0x2F, 0x78,
            0x2E, 0x6C, 0x6F, 0x67, path2);
        assert(bytes_prefix_eq(seq![0x2Fu8, 0x74u8, 0x64u8], path2));
        assert(strip_prefix_spec(seq![0x2F, 0x74, 0x64], path2)
            == Some(seq![0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x78, 0x2E,
                0x6C, 0x6F, 0x67]));
        assert(gi_strip_spec(seq![0x2F, 0x74, 0x64], path2)
            == seq![0x66, 0x6F, 0x6F, 0x2F, 0x78, 0x2E, 0x6C, 0x6F,
                0x67]);
        gi_slot_empty_eval(
            ig_foo.nodes@[0].custom_ignore_matcher.globs@,
            ig_foo.nodes@[0].custom_ignore_matcher.set.registered@,
            ig_foo.nodes@[0].custom_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(
            ig_foo.nodes@[0].ignore_matcher.globs@,
            ig_foo.nodes@[0].ignore_matcher.set.registered@,
            ig_foo.nodes@[0].ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(
            ig_foo.nodes@[0].git_ignore_matcher.globs@,
            ig_foo.nodes@[0].git_ignore_matcher.set.registered@,
            ig_foo.nodes@[0].git_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(
            ig_foo.nodes@[0].git_exclude_matcher.globs@,
            ig_foo.nodes@[0].git_exclude_matcher.set.registered@,
            ig_foo.nodes@[0].git_exclude_matcher.root.bytes@,
            cand, false);
        assert(mi_scan(ig_foo.nodes@, 0, 1, mi_st_none(), cand, false,
            false) == mi_st_none());
        gi_slot_one_miss(
            foo_parent.custom_ignore_matcher.globs@,
            foo_parent.custom_ignore_matcher.set.registered@,
            foo_parent.custom_ignore_matcher.root.bytes@,
            path2,
            false,
            seq![0x66, 0x6F, 0x6F, 0x2F, 0x78, 0x2E, 0x6C, 0x6F,
                0x67],
            seq![0x73, 0x75, 0x62, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A],
        );
        gi_slot_empty_eval(foo_parent.ignore_matcher.globs@,
            foo_parent.ignore_matcher.set.registered@,
            foo_parent.ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(foo_parent.git_ignore_matcher.globs@,
            foo_parent.git_ignore_matcher.set.registered@,
            foo_parent.git_ignore_matcher.root.bytes@,
            path2, false);
        gi_slot_empty_eval(foo_parent.git_exclude_matcher.globs@,
            foo_parent.git_exclude_matcher.set.registered@,
            foo_parent.git_exclude_matcher.root.bytes@,
            path2, false);
        let st_none = MiScanSt {
            m_custom: None,
            m_ignore: None,
            m_gi: None,
            m_gi_exclude: None,
            saw_git: false,
        };
        assert(mi_step(foo_parent, mi_st_none(), path2, false, false)
            == st_none);
        assert(mi_step(foo_rootnd, st_none, path2, false, false)
            == st_none);
        assert(mi_scan(ig_foo.nodes@, 1, 3, mi_st_none(), path2,
            false, false) == st_none);
        gi_slot_empty_eval(ig_foo.inner.git_global_matcher.globs@,
            ig_foo.inner.git_global_matcher.set.registered@,
            ig_foo.inner.git_global_matcher.root.bytes@,
            cand, false);
        assert(mi_explicit(ig_foo.inner.explicit_ignores@, -1,
            cand, false) == None);
        assert(dir_mi_spec(&ig_foo, cand, false) == None);
    }
    let m2 = ig_foo.matched(b_x_log().as_slice(), false);
    assert(ig_m_view(&m2) == None);
    assert(m2 matches Match::None);
    true
}

/// The hidden dentry tier (matched_dir_entry's hidden layer, dir.rs
/// 514-524 -- on unix is_hidden_entry(dent) is pathutil's
/// is_hidden_path_only over dent.path()): a None verdict from the
/// pools fills with the Hidden Ignore verdict when opts.hidden is
/// on and the dentry path is hidden -- while the matched (non-
/// dentry) entry point NEVER consults hiddenness, and a hidden-off
/// ctx leaves the None verdict in place. No pool rule is needed:
/// the empty stacks decide None everywhere, so no mask admit is
/// quoted.
fn row_hidden_dentry() -> (r: bool)
    ensures r
{
    let head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: None };
    assert(ig_wf(&ig));
    // the hidden-off twin ctx
    let types_e2 = Types::empty();
    let ov_e2 = Override::empty();
    let gg_e2 = h_empty();
    let opts2 = IgnoreOptions {
        hidden: false,
        ignore: true,
        parents: true,
        git_global: true,
        git_ignore: true,
        git_exclude: true,
        ignore_case_insensitive: false,
        require_git: true,
    };
    let h_root = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let h_head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let inner2 = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e2,
        types: types_e2,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e2,
        opts: opts2,
    };
    let mut ns2: Vec<IgnoreNode> = Vec::new();
    ns2.push(h_head);
    ns2.push(h_root);
    let ig2 = Ignore { inner: inner2, nodes: ns2, absolute_base: None };
    assert(ig_wf(&ig2));

    proof {
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(iglib::dir::dir_matched_dentry_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal(iglib::pathutil::is_hidden_path_only_spec);
        reveal_with_fuel(first_abs, 4);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 3);
        reveal(iglib::pathutil::is_file_name_spec);
        // the pools stay empty for the hidden candidate
        let cand: Seq<u8> = seq![0x2E, 0x68, 0x69, 0x64];
        assert(ig_any_git(&ig) == false);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            cand, false);
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(), cand, false,
            false) == mi_st_none());
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            cand, false);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            cand, false) == None);
        assert(dir_mi_spec(&ig, cand, false) == None);
        assert(dir_matched_spec(&ig, cand, false) == None);
        // the hidden tier: opts.hidden on, the ".hid" spelling is
        // hidden, so the DENTRY entry point fills the None verdict
        assert(ig.inner.opts.hidden == true);
        assert(iglib::pathutil::is_hidden_path_only_spec(cand));
        assert(iglib::dir::dir_matched_dentry_spec(&ig, cand, false)
            == Some((false, IgmOrigSpec::Hidden)));
        let cand2: Seq<u8> = seq![0x2E, 0x68, 0x69, 0x64];
        // the hidden-off twin: the None verdict survives
        assert(ig2.inner.opts.hidden == false);
        assert(iglib::dir::dir_matched_dentry_spec(&ig2, cand2,
            false) == None);
    }
    // matched (non-dentry) never hides: None stays None
    let m1 = ig.matched(b_hid().as_slice(), false);
    assert(ig_m_view(&m1) == None);
    assert(m1 matches Match::None);
    // the dentry entry point hides on the default ctx
    let m2 = ig.matched_dir_entry(b_hid().as_slice(), false);
    assert(ig_m_view(&m2) == Some((false, IgmOrigSpec::Hidden)));
    assert(m2 matches Match::Ignore(_));
    // hidden-off: the dentry verdict stays None
    let m3 = ig2.matched_dir_entry(b_hid().as_slice(), false);
    assert(ig_m_view(&m3) == None);
    assert(m3 matches Match::None);
    true
}

/// The override short-circuit (dir.rs:541-544): "Match against the
/// override patterns. If an override matches regardless of
/// whether it's whitelist/ignore, then we quit and return that
/// result immediately. Overrides have the highest precedence."
/// The override store carries the line "foo" (non-'!' = the
/// override tier's inclusion glob; the wrapped gitignore store
/// keeps wl=false and the ov spec inverts), so "foo" is Whitelisted
/// with the Ov origin BEFORE any pool consultation (the .ignore
/// line "foo" below would have Ignored it -- never consulted).
fn row_override_shortcircuit() -> (r: bool)
    ensures r
{
    // the .ignore pool line "foo", never consulted
    let ig_m = h_matcher1(b_td_root(), b_ss_foo(), false, false);
    let head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: ig_m,
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    // the override store: line "foo" (wl=false inside the wrapped
    // gitignore; the ov tier inverts), empty matcher root
    let ov_store = h_matcher1(Vec::new(), b_ss_foo(), false, false);
    let ov_e = Override { inner: ov_store };
    let types_e = Types::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: None };
    assert(ig_wf(&ig));

    // the mask admit (S14 column line"foo": foo=1)
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x66, 0x6F, 0x6F]) == true);

    proof {
        reveal(dir_matched_spec);
        reveal(iglib::dir::ov_slot_view);
        reveal(iglib::overrides::ov_matched_spec);
        reveal(gi_decide);
        reveal_with_fuel(gi_decide_from, 2);
        reveal(iglib::gitignore::gi_strip_spec);
        reveal(iglib::pathutil::is_file_name_spec);
        let cand: Seq<u8> = seq![0x66, 0x6F, 0x6F];
        // the override gate: registered non-empty
        assert(ig.inner.overrides == ov_e);
        assert(ig.inner.overrides.inner.set.registered@.len() == 1);
        // the ov decision: the wrapped store hits with wl=false,
        // the ov tier inverts to whitelist
        assert(gi_strip_spec(
            ig.inner.overrides.inner.root.bytes@, cand) == cand);
        gi_decide_from_step(
            ig.inner.overrides.inner.globs@,
            ig.inner.overrides.inner.set.registered@,
            cand,
            false,
            0,
        );
        assert(iglib::overrides::ov_matched_spec(&ig.inner.overrides,
            cand, false)
            == Some((true, Some((seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F,
                0x6F], seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
        assert(iglib::dir::ov_slot_view(&ig.inner.overrides, cand,
            false)
            == Some((true, IgmOrigSpec::Ov(Some((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None))))));
        // matched quits at the override tier: the Whitelist verdict
        // is returned before any pool consultation
        assert(dir_matched_spec(&ig, cand, false)
            == Some((true, IgmOrigSpec::Ov(Some((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None))))));
    }
    let m = ig.matched(b_foo().as_slice(), false);
    assert(ig_m_view(&m)
        == Some((true, IgmOrigSpec::Ov(Some((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], false, false, None))))));
    assert(m matches Match::Whitelist(_));
    true
}

/// The types tier (dir.rs:563-571 -- upstream dir.rs:564's
/// `if !self.inner.types.is_empty()` gate and the
/// types.matched consumption): with a selected "log" def (the glob
/// "*.log"), "x.log" is Whitelisted with the Ty def-name origin,
/// a non-matching file with a selection present is Ignored with the
/// unmatched-none origin, and a matched .ignore Ignore still wins
/// over the types tier (the mi early-return of dir_matched_spec).
/// The types-glob pairs are ANALOG admits: the S14 column line
/// "*.log" quotes the rewritten actual "**/*.log" for the same
/// candidates (x.log=1 / file.log=0 for the *.log-family shapes);
/// the raw def glob "*.log" against the file NAME is the types
/// twin's own spelling of that family.
fn row_types_tier() -> (r: bool)
    ensures r
{
    // the selected "log" def with the glob "*.log"
    let mut dglobs: Vec<Vec<u8>> = Vec::new();
    dglobs.push(b_star_log());
    let fdef = FileTypeDef { name: b_log(), globs: dglobs };
    let mut defs: Vec<FileTypeDef> = Vec::new();
    defs.push(fdef);
    let mut dglobs2: Vec<Vec<u8>> = Vec::new();
    dglobs2.push(b_star_log());
    let fdef3 = FileTypeDef { name: b_log(), globs: dglobs2 };
    let sel = Selection::Select(b_log(), fdef3);
    let mut sels: Vec<Selection<FileTypeDef>> = Vec::new();
    sels.push(sel);
    let rr = h_reg_vec(b_star_log());
    let mut regs: Vec<RegisteredGlob> = Vec::new();
    regs.push(rr);
    let mut gts_isel: Vec<usize> = Vec::new();
    gts_isel.push(0);
    let mut gts_iglob: Vec<usize> = Vec::new();
    gts_iglob.push(0);
    let types_e = Types {
        defs,
        selections: sels,
        has_selected: true,
        gts_isel,
        gts_iglob,
        set: GlobSetFace { registered: regs },
    };
    // the .ignore pool line "foo" (the mi-early-return leg)
    let ig_m = h_matcher1(b_td_root(), b_ss_foo(), false, false);
    let head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: ig_m,
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: None };
    assert(ig_wf(&ig));

    // the mask admits: pool exact + the types glob (ANALOG family)
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x66, 0x6F, 0x6F]) == true);
    assume(glob_pat_matches(seq![0x2A, 0x2E, 0x6C, 0x6F, 0x67], false, seq![0x78, 0x2E, 0x6C, 0x6F, 0x67]) == true);
    assume(glob_pat_matches(seq![0x2A, 0x2E, 0x6C, 0x6F, 0x67], false, seq![0x62, 0x61, 0x7A]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x78, 0x2E, 0x6C, 0x6F, 0x67]) == false);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x62, 0x61, 0x7A]) == false);

    // "foo": the .ignore Ignore wins before the types tier
    proof {
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal(iglib::dir::ty_slot_view);
        reveal(iglib::types::ty_matched_spec);
        reveal(iglib::types::ty_decide_at);
        reveal_with_fuel(iglib::types::ty_decide_at, 2);
        reveal(iglib::pathutil::file_name_spec);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        reveal_with_fuel(first_abs, 4);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 3);
        let cand: Seq<u8> = seq![0x66, 0x6F, 0x6F];
        assert(ig_any_git(&ig) == false);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            cand, false);
        assert(gi_strip_spec(
            ig.nodes@[0].ignore_matcher.root.bytes@, cand) == cand);
        gi_slot_one_eval(
            ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            cand,
            false,
            cand,
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            cand, false);
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(), cand, false,
            false)
            == MiScanSt {
                m_custom: None,
                m_ignore: Some((false, IgmOrigSpec::Gi((
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    false, false, None)))),
                m_gi: None,
                m_gi_exclude: None,
                saw_git: false,
            });
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            cand, false);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            cand, false) == None);
        assert(dir_mi_spec(&ig, cand, false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
        // the mi early-return: the ty tier is never the answer
        assert(dir_matched_spec(&ig, cand, false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
    }
    let m1 = ig.matched(b_foo().as_slice(), false);
    assert(ig_m_view(&m1)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], false, false, None)))));
    assert(m1 matches Match::Ignore(_));

    // "x.log": the types tier whitelists (the Ty def-name origin)
    proof {
        let cand: Seq<u8> = seq![0x78, 0x2E, 0x6C, 0x6F, 0x67];
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            cand, false);
        assert(gi_strip_spec(
            ig.nodes@[0].ignore_matcher.root.bytes@, cand) == cand);
        gi_slot_one_miss(
            ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            cand,
            false,
            cand,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            cand, false);
        assert(dir_mi_spec(&ig, cand, false) == None);
        // the ty tier: the selected def matches the file name
        assert(ig.inner.types.set.registered@.len() == 1);
        assert(iglib::pathutil::file_name_spec(cand)
            == Some(seq![0x78, 0x2E, 0x6C, 0x6F, 0x67]));
        assert(ig.inner.types.set.registered@[0].pattern@
            == seq![0x2Au8, 0x2Eu8, 0x6Cu8, 0x6Fu8, 0x67u8]);
        assert(iglib::types::ty_decide_at(&ig.inner.types,
            seq![0x78, 0x2E, 0x6C, 0x6F, 0x67], 0)
            == Some((false, seq![0x6C, 0x6F, 0x67])));
        assert(iglib::dir::ty_slot_view(&ig.inner.types, cand, false)
            == Some((true, IgmOrigSpec::Ty(Some(seq![0x6C, 0x6F,
                0x67])))));
        assert(dir_matched_spec(&ig, cand, false)
            == Some((true, IgmOrigSpec::Ty(Some(seq![0x6C, 0x6F,
                0x67])))));
    }
    let m2 = ig.matched(b_x_log().as_slice(), false);
    assert(ig_m_view(&m2)
        == Some((true, IgmOrigSpec::Ty(Some(seq![0x6C, 0x6F, 0x67])))));
    assert(m2 matches Match::Whitelist(_));

    // "baz": a selection is present and the file matches nothing,
    // so the ty tier Ignored with the unmatched-none origin
    proof {
        let cand: Seq<u8> = seq![0x62, 0x61, 0x7A];
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            cand, false);
        assert(gi_strip_spec(
            ig.nodes@[0].ignore_matcher.root.bytes@, cand) == cand);
        gi_slot_one_miss(
            ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            cand,
            false,
            cand,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            cand, false);
        assert(dir_mi_spec(&ig, cand, false) == None);
        assert(iglib::pathutil::file_name_spec(cand)
            == Some(seq![0x62, 0x61, 0x7A]));
        assert(iglib::types::ty_decide_at(&ig.inner.types,
            seq![0x62, 0x61, 0x7A], 0) matches None);
        assert(ig.inner.types.has_selected);
        assert(iglib::dir::ty_slot_view(&ig.inner.types, cand, false)
            == Some((false, IgmOrigSpec::Ty(None))));
        assert(dir_matched_spec(&ig, cand, false)
            == Some((false, IgmOrigSpec::Ty(None))));
    }
    let m3 = ig.matched(b_baz().as_slice(), false);
    assert(ig_m_view(&m3) == Some((false, IgmOrigSpec::Ty(None))));
    assert(m3 matches Match::Ignore(_));
    true
}

/// absolute_parent_repository_without_rules (dir.rs:1492-1508):
/// rules INSIDE the repository's search root fire through the
/// first scan while the after-barrier scan stays CLOSED
/// (has_absolute_parent_rules false: nothing above the root),
/// even with the abs base attached. Upstream writes "blocked" at
/// root/.gitignore and asserts root/blocked is Ignore and
/// root/other is None; re-spelled: the head's .gitignore line
/// "foo" with the matcher root "/td/x", the absolute candidates
/// "/td/x/foo" (Ignore) and "/td/x/baz" (None) -- the root strip
/// drops the "/td/x" prefix, so the masked pairs are the S14
/// one-component quotes exactly.
fn row_repository_without_rules() -> (r: bool)
    ensures r
{
    // the search-root's own .gitignore: line "foo", root "/td/x"
    let root_gi = h_matcher1(b_slash_td_x(), b_ss_foo(), false, false);
    let head = IgnoreNode {
        dir: b_x(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: root_gi,
        git_exclude_matcher: h_empty(),
    };
    let parent = IgnoreNode {
        dir: b_slash_td(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let gg_e = h_empty();
    let opts = h_opts_default();
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_e,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(parent);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns,
        absolute_base: Some(b_slash_td_x()) };
    assert(ig_wf(&ig));

    // the mask admits (S14 columns line"foo": foo=1, baz=0)
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x66, 0x6F, 0x6F]) == true);
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x62, 0x61, 0x7A]) == false);

    proof {
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(first_abs, 5);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 4);
        reveal(iglib::pathutil::strip_prefix_spec);
        reveal(iglib::pathutil::bytes_prefix_eq);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        assert(ig.nodes@ == seq![head, parent, rootnd]);
        assert(ig.nodes@[0] == head);
        assert(ig.nodes@[1] == parent);
        assert(first_abs(ig.nodes@, 0) == 1);
        assert(ig.inner.opts.require_git == true);
        assert(any_has_git(ig.nodes@, 0) == true);
        assert(ig_any_git(&ig) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        // the after-barrier gate is CLOSED: the repository's own
        // rules do not stamp the head (upstream's OR fold fires only
        // when the parent walk itself found rule files)
        assert(ig.nodes@[0].has_absolute_parent_rules == false);
        assert(ig.absolute_base@ matches Some(_));
        // the absolute candidates under the search root: the store
        // root "/td/x" strips off, leaving the bare names
        let foo_abs: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x78,
            0x2F, 0x66, 0x6F, 0x6F];
        let baz_abs: Seq<u8> = seq![0x2F, 0x74, 0x64, 0x2F, 0x78,
            0x2F, 0x62, 0x61, 0x7A];
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            foo_abs, false);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            foo_abs, false);
        assert(gi_strip_spec(seq![0x2F, 0x74, 0x64, 0x2F, 0x78], foo_abs) == seq![0x66, 0x6F, 0x6F]);
        gstrip_p5t3(0x2F, 0x74, 0x64, 0x2F, 0x78, 0x66, 0x6F, 0x6F, foo_abs);

        gi_slot_one_eval(
            ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            foo_abs,
            false,
            seq![0x66, 0x6F, 0x6F],
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            foo_abs, false);
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(), foo_abs, false,
            true)
            == MiScanSt {
                m_custom: None,
                m_ignore: None,
                m_gi: Some((false, IgmOrigSpec::Gi((
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                    false, false, None)))),
                m_gi_exclude: None,
                saw_git: false,
            });
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            foo_abs, false);
        assert(ig.inner.explicit_ignores@.len() == 0);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            foo_abs, false) == None);
        assert(dir_mi_spec(&ig, foo_abs, false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            baz_abs, false);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            baz_abs, false);
        assert(gi_strip_spec(seq![0x2F, 0x74, 0x64, 0x2F, 0x78], baz_abs) == seq![0x62, 0x61, 0x7A]);
        gstrip_p5t3(0x2F, 0x74, 0x64, 0x2F, 0x78, 0x62, 0x61, 0x7A, baz_abs);

        gi_slot_one_miss(
            ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            baz_abs,
            false,
            seq![0x62, 0x61, 0x7A],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            baz_abs, false);
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(), baz_abs, false,
            true) == mi_st_none());
        gi_slot_empty_eval(ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            baz_abs, false);
        assert(mi_explicit(ig.inner.explicit_ignores@, -1,
            baz_abs, false) == None);
        assert(dir_mi_spec(&ig, baz_abs, false) == None);
    }
    let m1 = ig.matched(b_slash_td_x_foo().as_slice(), false);
    assert(ig_m_view(&m1)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], false, false, None)))));
    assert(m1 matches Match::Ignore(_));
    let m2 = ig.matched(b_slash_td_x_baz().as_slice(), false);
    assert(ig_m_view(&m2) == None);
    assert(m2 matches Match::None);
    true
}

/// The global-over-explicit or-order (the cascade tail of
/// dir.rs:709-714: m_gi_exclude.or(m_global).or(m_explicit) --
/// the global pool outranks the explicit pool): the global store's
/// "foo" line Ignored beats the explicit matcher's "!foo" whitelist
/// for the same candidate -- the verdict is the GLOBAL store's
/// entry, not the whitelisted explicit one. One exact S14 mask
/// pair serves both stores.
fn row_global_over_explicit() -> (r: bool)
    ensures r
{
    // the global store: line "foo", empty matcher root
    let gg_m = h_matcher1(Vec::new(), b_ss_foo(), false, false);
    // the explicit store: line "!foo" (a whitelist at the explicit
    // tier)
    let expl_m = h_matcher1(Vec::new(), b_ss_foo(), true, false);
    let head = IgnoreNode {
        dir: b_td(),
        is_absolute_parent: false,
        has_absolute_parent_rules: false,
        has_git: true,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let rootnd = IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty(),
        ignore_matcher: h_empty(),
        git_ignore_matcher: h_empty(),
        git_exclude_matcher: h_empty(),
    };
    let types_e = Types::empty();
    let ov_e = Override::empty();
    let opts = h_opts_default();
    let mut expls: Vec<Gitignore> = Vec::new();
    expls.push(expl_m);
    let inner = IgnoreInner {
        dir: Vec::new(),
        overrides: ov_e,
        types: types_e,
        global_gitignores_relative_to: None,
        explicit_ignores: expls,
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: gg_m,
        opts,
    };
    let mut ns: Vec<IgnoreNode> = Vec::new();
    ns.push(head);
    ns.push(rootnd);
    let ig = Ignore { inner, nodes: ns, absolute_base: None };
    assert(ig_wf(&ig));

    // the mask admit (S14 column line"foo": foo=1 -- one pair
    // serves both the global and the explicit stores)
    assume(glob_pat_matches(seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F], false, seq![0x66, 0x6F, 0x6F]) == true);

    proof {
        reveal(dir_matched_spec);
        reveal(dir_mi_spec);
        reveal(mi_scan);
        reveal(mi_step);
        reveal(mi_st_none);
        reveal(first_abs);
        reveal(any_has_git);
        reveal(ig_any_git);
        reveal(mi_explicit);
        reveal(or_hit);
        reveal(ig_has_any_rules_spec);
        reveal(gi_slot_view);
        reveal(strip_keep);
        reveal_with_fuel(mi_explicit, 3);
        reveal_with_fuel(first_abs, 4);
        reveal_with_fuel(any_has_git, 4);
        reveal_with_fuel(mi_scan, 3);
        reveal(iglib::pathutil::is_file_name_spec);
        reveal(iglib::gitignore::gi_strip_spec);
        let cand: Seq<u8> = seq![0x66, 0x6F, 0x6F];
        assert(ig.nodes@ == seq![head, rootnd]);
        assert(ig.nodes@[0] == head);
        assert(ig.inner.explicit_ignores@ == seq![expl_m]);
        assert(first_abs(ig.nodes@, 0) == 1);
        assert(ig.inner.opts.require_git == true);
        assert(any_has_git(ig.nodes@, 0) == true);
        assert(ig_any_git(&ig) == true);
        assert(iglib::dir::ig_has_any_rules_spec(&ig) == true);
        // the head's four empty slots
        gi_slot_empty_eval(ig.nodes@[0].custom_ignore_matcher.globs@,
            ig.nodes@[0].custom_ignore_matcher.set.registered@,
            ig.nodes@[0].custom_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(ig.nodes@[0].ignore_matcher.globs@,
            ig.nodes@[0].ignore_matcher.set.registered@,
            ig.nodes@[0].ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(ig.nodes@[0].git_ignore_matcher.globs@,
            ig.nodes@[0].git_ignore_matcher.set.registered@,
            ig.nodes@[0].git_ignore_matcher.root.bytes@,
            cand, false);
        gi_slot_empty_eval(ig.nodes@[0].git_exclude_matcher.globs@,
            ig.nodes@[0].git_exclude_matcher.set.registered@,
            ig.nodes@[0].git_exclude_matcher.root.bytes@,
            cand, false);
        let st_head_g = MiScanSt {
            m_custom: None,
            m_ignore: None,
            m_gi: None,
            m_gi_exclude: None,
            saw_git: true,
        };
        assert(mi_step(ig.nodes@[0], mi_st_none(), cand, false, true)
            == st_head_g);
        assert(mi_scan(ig.nodes@, 0, 1, mi_st_none(), cand, false,
            true) == st_head_g);
        assert(ig.absolute_base@ matches None);
        // the global store (empty root): strip leaves "foo" bare
        assert(gi_strip_spec(
            ig.inner.git_global_matcher.root.bytes@, cand) == cand);
        gi_slot_one_eval(
            ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            cand,
            false,
            cand,
            false,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        // the explicit store: "!foo" would whitelist
        assert(ig.inner.explicit_ignores@[0] == expl_m);
        assert(gi_strip_spec(
            ig.inner.explicit_ignores@[0].root.bytes@, cand) == cand);
        gi_slot_one_eval(
            ig.inner.explicit_ignores@[0].globs@,
            ig.inner.explicit_ignores@[0].set.registered@,
            ig.inner.explicit_ignores@[0].root.bytes@,
            cand,
            false,
            cand,
            true,
            false,
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
            seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
        );
        assert(mi_explicit(ig.inner.explicit_ignores@, 0,
            cand, false)
            == Some((true, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                true, false, None)))));
        // the cascade: the GLOBAL Ignore decision outranks the
        // explicit whitelist
        assert(dir_mi_spec(&ig, cand, false)
            == Some((false, IgmOrigSpec::Gi((
                seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8],
                seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F],
                false, false, None)))));
    }
    let m = ig.matched(b_foo().as_slice(), false);
    assert(ig_m_view(&m)
        == Some((false, IgmOrigSpec::Gi((
            seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], seq![0x2Au8, 0x2Au8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8], false, false, None)))));
    assert(m matches Match::Ignore(_));
    assert(!(m matches Match::Whitelist(_)));
    true
}
} // verus!

// Standalone-file invocation anchor (single-file verus runs need the
// empty main).
fn main() {}