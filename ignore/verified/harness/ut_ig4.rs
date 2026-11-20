//! ignore IG4 **harness zone** -- the types/defaults/overrides KAT
//! rows over the src-zone twin (batch IG4: TypesBuilder grammar +
//! Types::matched + definition faces, and the Override wrapper).
//!
//! Row families:
//! - UT-T: the decisive Types-matched rows of the 19 upstream
//!   vectors, constructed exactly as the runtime S12 prints them
//!   (the families' remaining columns are the S12 table); the mask
//!   admits quote the S12MASK column and every verdict asserts
//!   through the twin's `Match<Glob>` view family.
//! - UT-C: the DP17 corner rows (the empty-matcher arm, the
//!   is_dir bypass, and the no-file-name UnmatchedIgnore fallback).
//! - UT-O: the override tests through the twin's `Override::matched`
//!   face: the DP18 mirrors, the invert verdicts, the DP19
//!   dir-arm/fallback, and the proof-tier dp19_never_none.
//! - UT-B: the builder-face rows -- the name-validity corners of
//!   add() and the DP16 order-invariance instantiation.
//!
//! Admit discipline (inventory section 6): every GlobMatcher mask
//! admit below is pinned by the IG4 runtime columns
//! (ig4-driver-rows.txt S12MASK / S13MASK); the store constructions
//! quote the same driver's S12 defs / S13 actuals+counts columns; no
//! universal axiom.
//!
//! Running: ./third_party/verus-docker.sh verus --rlimit 300
//!   database/ignore/verified/harness/ut_ig4.rs

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/lib.rs"]
mod iglib;

use iglib::gitignore::{
    glob_pat_matches, glob_set_builder_build_leg, GlobSetBuilderFace, RegisteredGlob,
};
use iglib::overrides::{dp19_never_none, ov_match_view, Override};
use iglib::pathutil::file_name_spec;
use iglib::types::{
    builder_wf, dp16_same_polarity_invariance, globty_name_view,
    sel_def_name, sel_name, sel_negated, ty_decide_at, ty_matched_spec,
    ty_match_view, TyReg, Selection, Types, TypesBuilder, types_wf,
    FileTypeDef,
};
use iglib::{Error, Match, PathBytes};

verus! {

// The constructions derive their store views through the seq
// push/update index lemmas.
broadcast use vstd::seq::group_seq_axioms;

// =========================================================================
// byte helpers (single-element vec form)
// =========================================================================


fn bx_star_rs() -> (r: Vec<u8>)
    ensures r@ == seq![0x2A, 0x2E, 0x72, 0x73]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2A);
    v.push(0x2E);
    v.push(0x72);
    v.push(0x73);
    v
}

fn bx_librs() -> (r: Vec<u8>)
    ensures r@ == seq![0x6C, 0x69, 0x62, 0x2E, 0x72, 0x73]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x6C);
    v.push(0x69);
    v.push(0x62);
    v.push(0x2E);
    v.push(0x72);
    v.push(0x73);
    v
}

fn bx_mainrs() -> (r: Vec<u8>)
    ensures r@ == seq![0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x6D);
    v.push(0x61);
    v.push(0x69);
    v.push(0x6E);
    v.push(0x2E);
    v.push(0x72);
    v.push(0x73);
    v
}

fn bx_indexhtml() -> (r: Vec<u8>)
    ensures r@ == seq![0x69, 0x6E, 0x64, 0x65, 0x78, 0x2E, 0x68, 0x74, 0x6D, 0x6C]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x69);
    v.push(0x6E);
    v.push(0x64);
    v.push(0x65);
    v.push(0x78);
    v.push(0x2E);
    v.push(0x68);
    v.push(0x74);
    v.push(0x6D);
    v.push(0x6C);
    v
}

fn bx_rust() -> (r: Vec<u8>)
    ensures r@ == seq![0x72, 0x75, 0x73, 0x74]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x72);
    v.push(0x75);
    v.push(0x73);
    v.push(0x74);
    v
}

fn bx_adots() -> (r: Vec<u8>)
    ensures r@ == seq![0x61, 0x2F, 0x2E, 0x2E]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x61);
    v.push(0x2F);
    v.push(0x2E);
    v.push(0x2E);
    v
}

fn bx_rstarbar() -> (r: Vec<u8>)
    ensures r@ == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x62, 0x61, 0x72]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2A);
    v.push(0x2A);
    v.push(0x2F);
    v.push(0x2A);
    v.push(0x2E);
    v.push(0x62);
    v.push(0x61);
    v.push(0x72);
    v
}

fn bx_ars() -> (r: Vec<u8>)
    ensures r@ == seq![0x61, 0x2E, 0x72, 0x73]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x61);
    v.push(0x2E);
    v.push(0x72);
    v.push(0x73);
    v
}

fn bx_abar() -> (r: Vec<u8>)
    ensures r@ == seq![0x61, 0x2E, 0x62, 0x61, 0x72]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x61);
    v.push(0x2E);
    v.push(0x62);
    v.push(0x61);
    v.push(0x72);
    v
}

fn bx_rstar_rs() -> (r: Vec<u8>)
    ensures r@ == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x72, 0x73]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2A);
    v.push(0x2A);
    v.push(0x2F);
    v.push(0x2A);
    v.push(0x2E);
    v.push(0x72);
    v.push(0x73);
    v
}

fn bx_foors() -> (r: Vec<u8>)
    ensures r@ == seq![0x66, 0x6F, 0x6F, 0x2E, 0x72, 0x73]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v.push(0x2E);
    v.push(0x72);
    v.push(0x73);
    v
}

fn bx_fooc() -> (r: Vec<u8>)
    ensures r@ == seq![0x66, 0x6F, 0x6F, 0x2E, 0x63]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v.push(0x2E);
    v.push(0x63);
    v
}

fn bx_foo() -> (r: Vec<u8>)
    ensures r@ == seq![0x66, 0x6F, 0x6F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v
}

fn bx_root() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x68, 0x6F, 0x6D, 0x65, 0x2F, 0x61, 0x6E, 0x64, 0x72, 0x65, 0x77, 0x2F, 0x66, 0x6F, 0x6F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x68);
    v.push(0x6F);
    v.push(0x6D);
    v.push(0x65);
    v.push(0x2F);
    v.push(0x61);
    v.push(0x6E);
    v.push(0x64);
    v.push(0x72);
    v.push(0x65);
    v.push(0x77);
    v.push(0x2F);
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v
}

fn bx_afoo() -> (r: Vec<u8>)
    ensures r@ == seq![0x61, 0x2E, 0x66, 0x6F, 0x6F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x61);
    v.push(0x2E);
    v.push(0x66);
    v.push(0x6F);
    v.push(0x6F);
    v
}

fn bx_line() -> (r: Vec<u8>)
    ensures r@ == seq![0x6C, 0x69, 0x6E, 0x65]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x6C);
    v.push(0x69);
    v.push(0x6E);
    v.push(0x65);
    v
}

fn bx_starx() -> (r: Vec<u8>)
    ensures r@ == seq![0x2A, 0x2E, 0x78]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2A);
    v.push(0x2E);
    v.push(0x78);
    v
}

fn bx_all() -> (r: Vec<u8>)
    ensures r@ == seq![0x61, 0x6C, 0x6C]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x61);
    v.push(0x6C);
    v.push(0x6C);
    v
}

fn bx_empty() -> (r: Vec<u8>)
    ensures r@ == Seq::empty()
{
    let mut v: Vec<u8> = Vec::new();
    v
}

// =========================================================================
// UT-T -- the decisive Types-matched rows (S12 columns)
// =========================================================================


fn v1v(x: Vec<u8>) -> (r: Vec<Vec<u8>>)
    ensures
        r@.len() == 1,
        r@[0]@ == x@,
{
    let mut v: Vec<Vec<u8>> = Vec::new();
    v.push(x);
    v
}

fn v1reg(x: RegisteredGlob) -> (r: Vec<RegisteredGlob>)
    ensures
        r@.len() == 1,
        r@[0].pattern@ == x.pattern@,
        r@[0].case_insensitive == x.case_insensitive,
{
    let mut v: Vec<RegisteredGlob> = Vec::new();
    v.push(x);
    v
}

fn vn1u(x: usize) -> (r: Vec<usize>)
    ensures
        r@.len() == 1,
        r@[0] == x,
{
    let mut v: Vec<usize> = Vec::new();
    v.push(x);
    v
}

/// The one-selection Types state (S12's builder printout in twin
/// form: the def name + its single glob registered in def order,
/// the selection polarity per the vector).
fn one_sel_type(name: &Vec<u8>, glob: &Vec<u8>, iselect: bool)
    -> (r: Types)
    ensures
        types_wf(&r),
        r.set.registered@.len() == 1,
        r.selections@.len() == 1,
        r.has_selected == iselect,
        r.set.registered@[0].pattern@ == glob@,
        sel_negated(&r.selections@[0]) == !iselect,
        sel_name(&r.selections@[0]) == name@,
        sel_def_name(&r.selections@[0]) == name@,
{
    let def = FileTypeDef {
        name: vstd::slice::slice_to_vec(name.as_slice()),
        globs: v1v(vstd::slice::slice_to_vec(glob.as_slice())),
    };
    let reg = RegisteredGlob {
        pattern: vstd::slice::slice_to_vec(glob.as_slice()),
        case_insensitive: false,
    };
    let bset = GlobSetBuilderFace { registered: v1reg(reg) };
    let set = glob_set_builder_build_leg(&bset);
    let sname = vstd::slice::slice_to_vec(name.as_slice());
    let sel = if iselect {
        Selection::Select(sname, def)
    } else {
        Selection::Negate(sname, def)
    };
    let mut sels: Vec<Selection<FileTypeDef>> = Vec::new();
    sels.push(sel);
    Types {
        defs: Vec::new(),
        selections: sels,
        has_selected: iselect,
        gts_isel: vn1u(0),
        gts_iglob: vn1u(0),
        set,
    }
}



fn v1sel(x: Selection<FileTypeDef>) -> (r: Vec<Selection<FileTypeDef>>)
    ensures
        r@.len() == 1,
        sel_negated(&r@[0]) == sel_negated(&x),
        sel_name(&r@[0]) == sel_name(&x),
        sel_def_name(&r@[0]) == sel_def_name(&x),
{
    let mut v: Vec<Selection<FileTypeDef>> = Vec::new();
    v.push(x);
    v
}

fn one_sel_type_named_rust_rs(iselect: bool) -> (r: Types)
    ensures
        types_wf(&r),
        r.set.registered@.len() == 1,
        r.selections@.len() == 1,
        r.has_selected == iselect,
        r.set.registered@[0].pattern@ == seq![0x2A, 0x2E, 0x72, 0x73],
        sel_name(&r.selections@[0]) == seq![0x72, 0x75, 0x73, 0x74],
        sel_def_name(&r.selections@[0]) == seq![0x72, 0x75, 0x73, 0x74],
{
    let nm = bx_rust();
    let gb = bx_star_rs();
    one_sel_type(&nm, &gb, iselect)
}

/// UT-T match1 (S12 match1): select rust, "lib.rs" ->
/// whitelist[rust] (the S12MASK *.rs/lib.rs row).
fn kat_t_match1() {
    proof {
        assume(glob_pat_matches(seq![0x2A, 0x2E, 0x72, 0x73], false,
            seq![0x6C, 0x69, 0x62, 0x2E, 0x72, 0x73]) == true);
        reveal(ty_matched_spec);
        reveal(ty_match_view);
        reveal(globty_name_view);
        reveal_with_fuel(ty_decide_at, 4);
        reveal(file_name_spec);
    }
    let t = one_sel_type_named_rust_rs(true);
    let m = t.matched(bx_librs().as_slice(), false);
    assert(ty_match_view(&m)
        == Some((true, Some(seq![0x72, 0x75, 0x73, 0x74]))));
}

/// UT-T matchnot1 (S12 matchnot1): select rust, "index.html": no
/// mask hit, has_selected true -- the UnmatchedIgnore fallback of
/// types.rs:297-299.
fn kat_t_matchnot1() {
    proof {
        assume(glob_pat_matches(seq![0x2A, 0x2E, 0x72, 0x73], false,
            seq![0x69, 0x6E, 0x64, 0x65, 0x78, 0x2E, 0x68, 0x74, 0x6D,
                0x6C]) == false);
    }
    let t = one_sel_type_named_rust_rs(true);
    let m = t.matched(bx_indexhtml().as_slice(), false);
    assert(ty_match_view(&m) == Some((false, None)));
}

/// UT-T match6 (S12 match6): negate-only, "main.rs": the negated
/// pattern hits -> Ignore[rust] (the payload names the negation
/// owner's def, types.rs:288-295).
fn kat_t_match6() {
    proof {
        assume(glob_pat_matches(seq![0x2A, 0x2E, 0x72, 0x73], false,
            seq![0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]) == true);
    }
    let t = one_sel_type_named_rust_rs(false);
    let m = t.matched(bx_mainrs().as_slice(), false);
    assert(ty_match_view(&m)
        == Some((false, Some(seq![0x72, 0x75, 0x73, 0x74]))));
}

/// UT-C match5 + the empty arm (S12 match5, DP17): the empty
/// matcher never matches (types.rs:270-271's set.is_empty arm).
fn kat_c_match5() {
    let t = Types::empty();
    assert(types_wf(&t));
    let m = t.matched(bx_indexhtml().as_slice(), false);
    assert(ty_match_view(&m) == None);
}

/// UT-C the DP17 is_dir bypass (S12 DP17 dir row): the is_dir arm
/// returns None before any mask consult (types.rs:270-271).
fn kat_c_dir_bypass() {
    proof {
        assume(glob_pat_matches(seq![0x2A, 0x2E, 0x72, 0x73], false,
            seq![0x6C, 0x69, 0x62, 0x2E, 0x72, 0x73]) == true);
    }
    let t = one_sel_type_named_rust_rs(true);
    let m = t.matched(bx_librs().as_slice(), true);
    assert(ty_match_view(&m) == None);
}

/// UT-C the DP17 no-file-name corner (S12 DP17 root/dots rows):
/// "a/.." has no file name (the pathutil `.`/`..` arm); with
/// has_selected the corner returns the UnmatchedIgnore
/// (types.rs:277-279). NB the driver's "/" root row lands on the
/// Some("")-name path (the twin's byte face), not this corner.
fn kat_c_nofilename() {
    assert(file_name_spec(seq![0x61, 0x2F, 0x2E, 0x2E]) matches None);
    let t = one_sel_type_named_rust_rs(true);
    let m = t.matched(bx_adots().as_slice(), false);
    assert(ty_match_view(&m) == Some((false, None)));
}

// =========================================================================
// UT-O -- the override rows (S13 columns) at the twin's
// Override::matched face
// =========================================================================

/// The one-line Override state (S13's actual/counts columns as twin
/// values; the mirrored counters per DP18: the wrapped Gitignore's
/// counts are the OVERRIDE-READ pair swapped, overrides.rs:70-77).
fn one_line_ov(
    actual: &Vec<u8>,
    wl: bool,
    n_gi_ignore: u64,
    n_gi_white: u64,
) -> (r: Override)
    ensures
        r.inner.set.registered@.len() == 1,
        r.inner.globs@.len() == 1,
        r.inner.num_ignores == n_gi_ignore,
        r.inner.num_whitelists == n_gi_white,
        r.inner.set.registered@[0].pattern@ == actual@,
        !r.inner.set.registered@[0].case_insensitive,
        r.inner.globs@[0].is_whitelist == wl,
        r.inner.globs@[0].is_only_dir == false,
{
    let g = iglib::gitignore::Glob {
        from: None,
        original: bx_line(),
        actual: vstd::slice::slice_to_vec(actual.as_slice()),
        is_whitelist: wl,
        is_only_dir: false,
    };
    let reg = RegisteredGlob {
        pattern: vstd::slice::slice_to_vec(actual.as_slice()),
        case_insensitive: false,
    };
    let bset = GlobSetBuilderFace { registered: v1reg(reg) };
    let set = glob_set_builder_build_leg(&bset);
    let mut gs: Vec<iglib::gitignore::Glob> = Vec::new();
    gs.push(g);
    let gi = iglib::gitignore::Gitignore {
        set,
        root: PathBytes { bytes: bx_root() },
        globs: gs,
        num_ignores: n_gi_ignore,
        num_whitelists: n_gi_white,
    };
    Override { inner: gi }
}

/// UT-O empty (S13 empty): never matches; counts 0/0.
fn kat_o_empty() {
    let o = Override::empty();
    let ni = o.num_ignores();
    let nw = o.num_whitelists();
    assert(ni == 0);
    assert(nw == 0);
    let m = o.matched(bx_afoo().as_slice(), false);
    assert(ov_match_view(m) matches None);
}

/// UT-O only_ignores (S13 only_ignores): ['!*.bar'] -- the wrapped
/// store is one WL record ('!'-line) with gi counts (0 ignore, 1
/// white); the DP18 mirrors read Override.num_ignores == 1 and
/// num_whitelists == 0 -- so the DP19 fallback never fires:
/// none("a.rs") even at is_dir=false, ignore("a.bar").
fn kat_o_only_ignores() {
    proof {
        assume(glob_pat_matches(
            seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x62, 0x61, 0x72], false,
            seq![0x61, 0x2E, 0x72, 0x73]) == false);
        assume(glob_pat_matches(
            seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x62, 0x61, 0x72], false,
            seq![0x61, 0x2E, 0x62, 0x61, 0x72]) == true);
    }
    let o = { let act = bx_rstarbar(); one_line_ov(&act, true, 0, 1) };
    // the DP18 mirror pair (S13: only_ignores num_ignores=1
    // num_whitelists=0)
    let ni = o.num_ignores();
    let nw = o.num_whitelists();
    assert(ni == 1);
    assert(nw == 0);
    let m1 = o.matched(bx_ars().as_slice(), false);
    assert(ov_match_view(m1) matches None);
    let m2 = o.matched(bx_abar().as_slice(), false);
    assert(ov_match_view(m2) matches Some((false, Some(_))));
}

/// UT-O allow_directories (S13 allow_directories): ['*.rs'] -- one
/// '!'-free line: gi counts (1 ignore, 0 white); the DP18 mirrors
/// read Override.num_ignores == 0 / num_whitelists == 1; the DP19
/// dir arm keeps the unmatched-dir candidate None while the
/// unmatched-file candidate tumbles into the fallback.
fn kat_o_allow_directories() {
    proof {
        assume(glob_pat_matches(
            seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x72, 0x73], false,
            seq![0x66, 0x6F, 0x6F, 0x2E, 0x72, 0x73]) == true);
        assume(glob_pat_matches(
            seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x72, 0x73], false,
            seq![0x66, 0x6F, 0x6F, 0x2E, 0x63]) == false);
        assume(glob_pat_matches(
            seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x72, 0x73], false,
            seq![0x66, 0x6F, 0x6F]) == false);
    }
    let o = { let act = bx_rstar_rs(); one_line_ov(&act, false, 1, 0) };
    // the DP18 mirror pair (S13: allow_directories num_ignores=0
    // num_whitelists=1)
    let ni = o.num_ignores();
    let nw = o.num_whitelists();
    assert(ni == 0);
    assert(nw == 1);
    // the hit: '!'-free line inverts to whitelist
    let m1 = o.matched(bx_foors().as_slice(), false);
    assert(ov_match_view(m1) matches Some((true, Some(_))));
    // unmatched non-dir: the DP19 fallback
    let m2 = o.matched(bx_fooc().as_slice(), false);
    assert(ov_match_view(m2) matches Some((false, None)));
    // unmatched dir: None (the !is_dir arm of the fallback)
    let m3 = o.matched(bx_foo().as_slice(), true);
    assert(ov_match_view(m3) matches None);
}

/// UT-O dp19 proof tier: with an '!'-free line present
/// (ov.num_whitelists() > 0) and !is_dir, matched never returns
/// None (dp19_never_none instantiated on the constructed state).
fn kat_o_dp19() {
    let o = { let act = bx_rstar_rs(); one_line_ov(&act, false, 1, 0) };
    proof {
        dp19_never_none(&o, seq![0x61, 0x2E, 0x72, 0x73], false);
    }
    let m = o.matched(bx_ars().as_slice(), false);
    assert(ov_match_view(m) matches Some(_));
}

// =========================================================================
// UT-B -- the builder-face rows
// =========================================================================

/// UT-B name corners (S12 add-validity + empty/all rows): "all"
/// rejects with no mutation; the EMPTY name ACCEPTS (the vacuous
/// `chars().all` of types.rs:422 -- runtime-pinned S12
/// `empty-name ok=true`; the twin's bounded face mirrors it).
fn kat_b_name_corners() {
    let mut b = TypesBuilder::new();
    assert(builder_wf(&b));
    let r_all = b.add(b"all", b"*.x");
    assert(r_all matches Err(e) && e matches Error::InvalidDefinition);
    assert(builder_wf(&b));
    let r_empty = b.add(b"", b"*.x");
    assert(r_empty matches Ok(_));
    assert(builder_wf(&b));
}

/// UT-B dp16 row (S12 dp16 all-probe): the 'all'-expansion
/// order-invariance instantiated on the 2-entry polarity-uniform
/// block -- the two map insertion orders of the probe land in the
/// lemma's premises and the verdict-equality conclusion.
fn kat_b_dp16() {
    proof {
        let rs = TyReg {
            pattern: seq![0x2A, 0x2E, 0x72, 0x73],
            case_insensitive: false,
            negated: false,
            def_name: seq![0x72, 0x75, 0x73, 0x74],
        };
        let js = TyReg {
            pattern: seq![0x2A, 0x2E, 0x6A, 0x73],
            case_insensitive: false,
            negated: false,
            def_name: seq![0x6A, 0x73],
        };
        let regs1 = Seq::empty().push(rs).push(js);
        let regs2 = Seq::empty().push(js).push(rs);
        dp16_same_polarity_invariance(
            regs1, regs2, seq![0x6C, 0x69, 0x62, 0x2E, 0x72, 0x73], 0);
    }
}

// =========================================================================
// run-anywhere anchor: the verus harness is a static unit
// =========================================================================

fn main() {}

} // verus!
