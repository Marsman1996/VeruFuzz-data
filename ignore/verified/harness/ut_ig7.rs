//! ignore IG7 **harness zone** -- the walk.rs KAT rows over the
//! src-zone twin (batch IG7 deferred-3: the `DirEntry` family, the
//! `Error::from_walkdir` mapping, `skip_filesize`, the first skip
//! tier, the `WalkBuilder` min/max mutual clamps, and the
//! `WalkEventIter` Exit cascade, over the IG6 `Ignore` spine).
//!
//! Row families (every row cites its upstream anchor in walk.rs of
//! the pinned crate `ignore` 0.4.34; the runtime backstop is the
//! IG6 205/0 replay recorded in the IG7 batch notes):
//! - UT-D: the `DirEntry` three-arm value rows -- the stdin arm's
//!   full accessor table, and the walkdir-arm / raw-arm accessor
//!   posts over the trusted walkdir/fs data faces;
//! - UT-N: the raw construction + name-fallback geometry (`/`,
//!   `/a/`, `/a/..`, `x/..`) -- the external_body contract legs
//!   (raw_file_name / ifile_name, the #IG-33 membrane) consumed
//!   per-instance through the shared `name_rule` post, with the
//!   spec side evaluated by real proofs over the pathutil twin's
//!   memrchr bridges;
//! - UT-C: the min/max depth clamp order-flip vectors
//!   (min(2)-then-max(1) and max(1)-then-min(2));
//! - UT-S: the skip_filesize over / boundary / under / no-stat
//!   table and the should_skip_entry first-tier verdict table;
//! - UT-F: the Error::from_walkdir mapping rows (the double-Some
//!   Loop short-circuit, the io arm with and without the WithPath
//!   wrap);
//! - UT-W: the WalkEventIter trace rows (the Exit cascade model
//!   consumed per-instance over wf abstract streams).
//!
//! Discipline: no new admits anywhere below -- every row consumes
//! real posts, per-instance contract posts, or constructed record
//! faces (whose field carries are proven at construction); the
//! WalkEventIter rows consume the machine's own conditional model
//! posts (the emitted kind is not characterized by the we_next
//! contract, so the rows pin the per-level Exit model laws, not
//! the hull membership).
//!
//! Running: ./third_party/verus-docker.sh verus --rlimit 300
//!   database/ignore/verified/harness/ut_ig7.rs

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/lib.rs"]
mod iglib;

use iglib::dir::{IgmOrig, IgmPayload};
use iglib::gitignore::flat_subrange;
use iglib::pathutil::{
    memrchr_spec_none_bridge, memrchr_spec_some_bridge,
};
use iglib::walk::{
    from_walkdir, name_rule, should_skip_entry_first,
    should_skip_verdict, skip_filesize, stdin_bytes, stdin_lit,
    wio_view, wloop_view, wstream_wf, DirEntry, DirEntryInner,
    DirEntryRaw, FileTypeFace, WalkBuilder, WalkEvent,
    WalkEventIter, WalkdirDentFace, WalkdirErrFace, WdEventFace,
};
use iglib::{IoErrorFace, Match};

verus! {

// The Vec push-index bookkeeping (one broadcast per module).
broadcast use vstd::seq::group_seq_axioms;

// =========================================================================
// byte-literal carriers (parametric push chains, the ut_ig5 style)
// =========================================================================

fn b1(a: u8) -> (r: Vec<u8>)
    ensures r@ == seq![a]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(a);
    v
}

fn b2(a: u8, c: u8) -> (r: Vec<u8>)
    ensures r@ == seq![a, c]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(a);
    v.push(c);
    v
}

fn b3(a: u8, c: u8, d: u8) -> (r: Vec<u8>)
    ensures r@ == seq![a, c, d]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(a);
    v.push(c);
    v.push(d);
    v
}

fn b4(a: u8, c: u8, d: u8, e: u8) -> (r: Vec<u8>)
    ensures r@ == seq![a, c, d, e]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(a);
    v.push(c);
    v.push(d);
    v.push(e);
    v
}

fn b5(a: u8, c: u8, d: u8, e: u8, f: u8) -> (r: Vec<u8>)
    ensures r@ == seq![a, c, d, e, f]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(a);
    v.push(c);
    v.push(d);
    v.push(e);
    v.push(f);
    v
}

// =========================================================================
// record-face constructors (full field carries, the h_* style)
// =========================================================================

/// A file-type face with the three bits pinned.
fn h_ft(is_dir: bool, is_file: bool, is_symlink: bool)
    -> (r: FileTypeFace)
    ensures
        r.is_dir == is_dir,
        r.is_file == is_file,
        r.is_symlink == is_symlink,
{
    FileTypeFace { is_dir, is_file, is_symlink }
}

/// A walkdir entry face with every field carried (the trusted data
/// face of the walkdir arm).
fn h_wdent(
    path: Vec<u8>,
    depth: usize,
    ty: FileTypeFace,
    is_symlink: bool,
    ino: Option<u64>,
) -> (r: WalkdirDentFace)
    ensures
        r.path@ == path@,
        r.depth == depth,
        r.ty.is_dir == ty.is_dir,
        r.ty.is_file == ty.is_file,
        r.ty.is_symlink == ty.is_symlink,
        r.is_symlink == is_symlink,
        r.ino == ino,
{
    WalkdirDentFace { path, depth, ty, is_symlink, ino }
}

/// One ok event (a walkdir entry yield): single-sided ok, the depth
/// and directory bits carried for the machine's reads.
fn h_ev_ok(path: Vec<u8>, depth: usize, ty: FileTypeFace)
    -> (r: WdEventFace)
    ensures
        r.ok matches Some(_),
        r.err matches None,
        r.ok matches Some(d) ==> (d.path@ == path@
            && d.depth == depth
            && d.ty.is_dir == ty.is_dir
            && d.ty.is_file == ty.is_file
            && d.ty.is_symlink == ty.is_symlink),
{
    WdEventFace {
        ok: Some(WalkdirDentFace {
            path,
            depth,
            ty,
            is_symlink: false,
            ino: None,
        }),
        err: None,
    }
}

/// One err event (a walkdir error yield): single-sided err, the
/// error depth carried for the machine's depth read.
fn h_ev_err(depth: usize) -> (r: WdEventFace)
    ensures
        r.ok matches None,
        r.err matches Some(_),
        r.err matches Some(e) ==> e.depth == depth,
{
    WdEventFace {
        ok: None,
        err: Some(WalkdirErrFace {
            depth,
            loop_ancestor: None,
            path: None,
            io: IoErrorFace { repr: 0 },
        }),
    }
}

/// The verdict payload with the hidden-pool origin marker (the
/// origin decoration is outside the first tier's value table, so
/// the arm marker alone suffices).
fn h_payload_hidden() -> (r: IgmPayload)
    ensures r.orig matches IgmOrig::Hidden,
{
    IgmPayload {
        gi_glob: None,
        ov_glob: None,
        ty_glob: None,
        orig: IgmOrig::Hidden,
    }
}

// =========================================================================
// UT-N spec helpers: the name_rule geometry evaluated by real
// proofs (Origin walk.rs:314-316: the trailing-slash trim, the
// memrchr split and the empty/`..` whole-path fallbacks)
// =========================================================================

/// "/" has no file name below the root separator: the split's name
/// is empty, so the whole path returns.
proof fn nr_root_slash()
    ensures name_rule(seq![0x2F]) == seq![0x2F]
{
    assert(seq![0x2Fu8].len() == 1);
    assert(seq![0x2Fu8][0] == 0x2F);
    memrchr_spec_some_bridge(seq![0x2F], 0x2F, 0);
    // the name subrange below the separator is empty: len 1 - 1 = 0
    vstd::seq::lemma_seq_subrange_len(seq![0x2Fu8], 1, 1);
}

/// "/a/": the trailing separator trims to "/a", the split below
/// the root separator yields the name "a".
proof fn nr_a_slash()
    ensures name_rule(seq![0x2F, 0x61, 0x2F]) == seq![0x61]
{
    assert(seq![0x2Fu8, 0x61, 0x2F].len() == 3);
    assert(seq![0x2Fu8, 0x61, 0x2F][2] == 0x2F);
    // the trailing-slash trim: "/" + "a"
    flat_subrange(
        seq![0x2F, 0x61, 0x2F], 0, 2, seq![0x2F, 0x61]);
    assert(seq![0x2Fu8, 0x61][0] == 0x2F);
    assert(seq![0x2Fu8, 0x61][1] == 0x61);
    memrchr_spec_some_bridge(seq![0x2F, 0x61], 0x2F, 0);
    // the name subrange below the separator is "a"
    flat_subrange(seq![0x2F, 0x61], 1, 2, seq![0x61]);
    // len 1 is neither empty nor the ".." name
    assert(seq![0x61u8].len() == 1);
}

/// "/a/..": no trailing separator, the split after the last
/// separator is exactly "..", so the whole path returns.
proof fn nr_slash_a_dotdot()
    ensures
        name_rule(seq![0x2F, 0x61, 0x2F, 0x2E, 0x2E])
            == seq![0x2F, 0x61, 0x2F, 0x2E, 0x2E]
{
    assert(seq![0x2Fu8, 0x61, 0x2F, 0x2E, 0x2E].len() == 5);
    assert(seq![0x2Fu8, 0x61, 0x2F, 0x2E, 0x2E][2] == 0x2F);
    assert(seq![0x2Fu8, 0x61, 0x2F, 0x2E, 0x2E][3] == 0x2E);
    assert(seq![0x2Fu8, 0x61, 0x2F, 0x2E, 0x2E][4] == 0x2E);
    memrchr_spec_some_bridge(
        seq![0x2F, 0x61, 0x2F, 0x2E, 0x2E], 0x2F, 2);
    // the name subrange after the last separator is exactly ".."
    flat_subrange(
        seq![0x2F, 0x61, 0x2F, 0x2E, 0x2E], 3, 5,
        seq![0x2E, 0x2E]);
}

/// "x/..": the same ".." fallback behind a relative root.
proof fn nr_x_dotdot()
    ensures
        name_rule(seq![0x78, 0x2F, 0x2E, 0x2E])
            == seq![0x78, 0x2F, 0x2E, 0x2E]
{
    assert(seq![0x78u8, 0x2F, 0x2E, 0x2E].len() == 4);
    assert(seq![0x78u8, 0x2F, 0x2E, 0x2E][1] == 0x2F);
    assert(seq![0x78u8, 0x2F, 0x2E, 0x2E][2] == 0x2E);
    assert(seq![0x78u8, 0x2F, 0x2E, 0x2E][3] == 0x2E);
    memrchr_spec_some_bridge(
        seq![0x78, 0x2F, 0x2E, 0x2E], 0x2F, 1);
    flat_subrange(
        seq![0x78, 0x2F, 0x2E, 0x2E], 2, 4, seq![0x2E, 0x2E]);
}

/// "a/foo": the plain name split (no trim, no fallback).
proof fn nr_a_foo()
    ensures
        name_rule(seq![0x61, 0x2F, 0x66, 0x6F, 0x6F])
            == seq![0x66, 0x6F, 0x6F]
{
    assert(seq![0x61u8, 0x2F, 0x66, 0x6F, 0x6F].len() == 5);
    assert(seq![0x61u8, 0x2F, 0x66, 0x6F, 0x6F][1] == 0x2F);
    assert(seq![0x61u8, 0x2F, 0x66, 0x6F, 0x6F][2] == 0x66);
    assert(seq![0x61u8, 0x2F, 0x66, 0x6F, 0x6F][3] == 0x6F);
    assert(seq![0x61u8, 0x2F, 0x66, 0x6F, 0x6F][4] == 0x6F);
    memrchr_spec_some_bridge(
        seq![0x61, 0x2F, 0x66, 0x6F, 0x6F], 0x2F, 1);
    flat_subrange(
        seq![0x61, 0x2F, 0x66, 0x6F, 0x6F], 2, 5,
        seq![0x66, 0x6F, 0x6F]);
    // len 3 is neither empty nor the ".." name
    assert(seq![0x66u8, 0x6F, 0x6F].len() == 3);
}

// =========================================================================
// UT-D: the DirEntry three-arm value rows
// =========================================================================

/// The stdin arm's full row (Origin walk.rs:107-109 new_stdin; the
/// accessor arm table walk.rs:37-105): path / is_stdin / depth /
/// file_name / file_type at the stdin sentinel.
fn row_dent_stdin_all() -> (r: bool)
    ensures r
{
    let de = DirEntry::wnew_stdin();
    // path (walk.rs:138-145: the "<stdin>" literal; the twin's own
    // carrier stdin_bytes() builds the same bytes)
    let p = de.wpath();
    let lit = stdin_bytes();
    assert(lit@ == p@);
    assert(p@ == seq![0x3C, 0x73, 0x74, 0x64, 0x69, 0x6E, 0x3E]);
    // is_stdin (walk.rs:165-170)
    let is = de.wis_stdin();
    assert(is == true);
    // depth (walk.rs:209-216: the stdin root sits at depth 0)
    let dep = de.wdepth();
    assert(dep == 0);
    // file_name (walk.rs:203-207: the same literal name)
    let nm = de.wfile_name();
    assert(nm@ == seq![0x3C, 0x73, 0x74, 0x64, 0x69, 0x6E, 0x3E]);
    // file_type (walk.rs:191-198: None only on the stdin arm)
    let ft = de.wfile_type();
    assert(ft matches None);
    // the attached error stays clear on the fresh construction
    // (walk.rs:89-95)
    let er = de.werror();
    assert(er matches None);
    // is_dir (walk.rs:230-233: the None file type reads false)
    let isd = de.wis_dir();
    assert(isd == false);
    true
}

/// The walkdir arm's value row (Origin walk.rs:111-113 new_walkdir;
/// the accessor arm table walk.rs:37-233): every accessor post over
/// one constructed entry face.
fn row_dent_walkdir_vals() -> (r: bool)
    ensures r
{
    let dent = h_wdent(
        b5(0x61, 0x2F, 0x66, 0x6F, 0x6F), 2,
        h_ft(false, true, false), false, Some(7),
    );
    let de = DirEntry {
        dent: DirEntryInner::Walkdir(dent),
        err: None,
    };
    // path (walk.rs:138-145: the face's own path)
    let p = de.wpath();
    assert(p@ == seq![0x61, 0x2F, 0x66, 0x6F, 0x6F]);
    // path_is_symlink (walk.rs:156-163)
    let sym = de.wpath_is_symlink();
    assert(sym == false);
    // is_stdin (walk.rs:165-170: false off the stdin arm)
    let is = de.wis_stdin();
    assert(is == false);
    // depth (walk.rs:209-216)
    let dep = de.wdepth();
    assert(dep == 2);
    // ino (walk.rs:218-227, the unix arm)
    let ino = de.wino();
    assert(ino == Some(7));
    // file_type (walk.rs:191-198: the face's own file type)
    let ft = de.wfile_type();
    assert(ft matches Some(_));
    assert((match ft {
        Some(t) => t.is_file,
        None => false,
    }) == true);
    assert((match ft {
        Some(t) => t.is_dir,
        None => false,
    }) == false);
    // is_dir (walk.rs:230-233)
    let isd = de.wis_dir();
    assert(isd == false);
    // the attached error (walk.rs:89-95)
    let er = de.werror();
    assert(er matches None);
    // file_name (walk.rs:200-207, the walkdir arm: the shared
    // fallback rule; "a/foo" splits to "foo")
    proof { nr_a_foo(); }
    let nm = de.wfile_name();
    assert(nm@ == seq![0x66, 0x6F, 0x6F]);
    true
}

// =========================================================================
// UT-N: the raw construction + name-fallback geometry rows
// (Origin walk.rs:327-335 from_entry for the construction; the
// contract legs raw_file_name / ifile_name at walk.rs:314-316)
// =========================================================================

/// "/" with the from-path construction (Origin walk.rs:327-335):
/// the face carry, every raw accessor post, and the empty-name
/// whole-path fallback through both the raw leg and the wrapper.
fn row_raw_root_slash() -> (r: bool)
    ensures r
{
    let raw = DirEntryRaw::raw_from_entry(
        1, b1(0x2F).as_slice(), false, true, false, true, Some(7));
    // the construction carry (the from_entry leg)
    assert(raw.depth == 1);
    assert(raw.raw_path@ == seq![0x2F]);
    assert(raw.ty.is_file == true);
    assert(raw.ty.is_symlink == false);
    assert(raw.follow_link == true);
    assert(raw.ino == Some(7));
    // the raw accessor posts (walk.rs:272-325)
    let rd = raw.raw_depth();
    assert(rd == 1);
    let ri = raw.raw_ino();
    assert(ri == Some(7));
    let pl = raw.raw_path_fn();
    assert(pl@ == seq![0x2F]);
    // the symlink shape (walk.rs:280-282:
    // ty.is_symlink || follow_link)
    let sym = raw.raw_path_is_symlink();
    assert(sym == true);
    // the file type (walk.rs:310-312)
    let ft = raw.raw_file_type();
    assert(ft.is_file == true);
    assert(ft.is_symlink == false);
    // the file name geometry (the raw_file_name contract leg,
    // walk.rs:314-316: "/" has no name below the root separator)
    proof { nr_root_slash(); }
    let nm = raw.raw_file_name();
    assert(nm@ == seq![0x2F]);
    // the same rule through the DirEntry wrapper (ifile_name's
    // Raw arm rides the identical contract)
    let de = DirEntry {
        dent: DirEntryInner::Raw(raw),
        err: None,
    };
    let nm2 = de.wfile_name();
    assert(nm2@ == seq![0x2F]);
    true
}

/// "/a/": the trailing-slash trim (Origin walk.rs:314-316: the
/// trailing separator is trimmed before the split).
fn row_raw_a_slash() -> (r: bool)
    ensures r
{
    let raw = DirEntryRaw::raw_from_entry(
        0, b3(0x2F, 0x61, 0x2F).as_slice(), false, true, false,
        false, None,
    );
    assert(raw.raw_path@ == seq![0x2F, 0x61, 0x2F]);
    assert(raw.depth == 0);
    proof { nr_a_slash(); }
    let nm = raw.raw_file_name();
    assert(nm@ == seq![0x61]);
    true
}

/// "/a/..": the ".." whole-path fallback (Origin walk.rs:314-316:
/// an empty or ".." final segment has no file name).
fn row_raw_slash_a_dotdot() -> (r: bool)
    ensures r
{
    let raw = DirEntryRaw::raw_from_entry(
        3, b5(0x2F, 0x61, 0x2F, 0x2E, 0x2E).as_slice(), false, true,
        false, false, None,
    );
    assert(raw.raw_path@ == seq![0x2F, 0x61, 0x2F, 0x2E, 0x2E]);
    proof { nr_slash_a_dotdot(); }
    let nm = raw.raw_file_name();
    assert(nm@ == seq![0x2F, 0x61, 0x2F, 0x2E, 0x2E]);
    true
}

/// "x/..": the same fallback behind a relative root (Origin
/// walk.rs:314-316).
fn row_raw_x_dotdot() -> (r: bool)
    ensures r
{
    let raw = DirEntryRaw::raw_from_entry(
        2, b4(0x78, 0x2F, 0x2E, 0x2E).as_slice(), false, true,
        false, false, None,
    );
    assert(raw.raw_path@ == seq![0x78, 0x2F, 0x2E, 0x2E]);
    proof { nr_x_dotdot(); }
    let nm = raw.raw_file_name();
    assert(nm@ == seq![0x78, 0x2F, 0x2E, 0x2E]);
    true
}

// =========================================================================
// UT-C: the min/max depth clamp order-flip rows (Origin
// walk.rs:730-753: both Some compare, max below min lifts to the
// min, min above max drops to the max; the upstream order-flip
// vector is min_depth(Some(2)).max_depth(Some(1)) at
// walk.rs:2533-2537, and the min-only vectors at :2511-2531)
// =========================================================================

/// min(2) then max(1): the max lifts to the min (the upstream
/// order-flip vector's terminal clamp).
fn row_clamp_min_then_max() -> (r: bool)
    ensures r
{
    let mut b = WalkBuilder::wnew(b1(0x2F).as_slice());
    // the fresh construction (walk.rs:551-554)
    assert(b.paths@.len() == 1);
    assert(b.max_depth matches None);
    assert(b.min_depth matches None);
    assert(b.max_filesize matches None);
    // min_depth(Some(2)) alone (walk.rs:744-753: no dual-Some
    // compare without a max, so nothing clamps)
    b.wmin_depth(Some(2));
    assert(b.min_depth == Some(2));
    assert(b.max_depth matches None);
    // the flip: max_depth(Some(1)) after min(2) lifts the max to
    // the min (walk.rs:730-739)
    b.wmax_depth(Some(1));
    assert(b.max_depth == Some(2));
    assert(b.min_depth == Some(2));
    // the untouched carries hold through both setters
    assert(b.paths@.len() == 1);
    assert(b.max_filesize matches None);
    assert(b.follow_links == false);
    assert(b.threads == 0);
    true
}

/// max(1) then min(2): the min drops to the max (the symmetric
/// order flip, walk.rs:744-753).
fn row_clamp_max_then_min() -> (r: bool)
    ensures r
{
    let mut b = WalkBuilder::wnew(b1(0x2F).as_slice());
    // max_depth(Some(1)) alone: min is None, nothing clamps
    // (walk.rs:730-739)
    b.wmax_depth(Some(1));
    assert(b.max_depth == Some(1));
    assert(b.min_depth matches None);
    // the flip: min_depth(Some(2)) after max(1) drops the min to
    // the max (walk.rs:744-753)
    b.wmin_depth(Some(2));
    assert(b.min_depth == Some(1));
    assert(b.max_depth == Some(1));
    true
}

// =========================================================================
// UT-S: the skip_FILESIZE table + the should_skip_entry first-tier
// verdict table
// =========================================================================

/// skip_filesize's stat table (Origin walk.rs:2058-2077: the strict
/// `>` against the limit, and the no-stat arm continues; the
/// upstream max_filesize vector's 500-limit run at
/// walk.rs:2541-2560 keeps the boundary and under rows and drops
/// the 600 rows).
fn row_skip_filesize_table() -> (r: bool)
    ensures r
{
    // over: a 600-byte stat vs the 500 limit skips
    let v_over = skip_filesize(500, Some(600));
    assert(v_over == true);
    // boundary: the equal size does NOT skip (the strict >)
    let v_edge = skip_filesize(500, Some(500));
    assert(v_edge == false);
    // under: the 400-byte row stays
    let v_under = skip_filesize(500, Some(400));
    assert(v_under == false);
    // no-stat: the consult failed, never skip
    let v_none = skip_filesize(500, None);
    assert(v_none == false);
    true
}

/// should_skip_entry's first-tier verdict table (Origin
/// walk.rs:2085-2098: the ignore verdict skips, the whitelist and
/// none verdicts continue; the real verdict law and the trusted
/// matched_dir_entry bridge consumed side by side).
fn row_should_skip_first_tier() -> (r: bool)
    ensures r
{
    // the ignore verdict skips (walk.rs:2091-2093)
    let mi = Match::Ignore(h_payload_hidden());
    let vi = should_skip_verdict(&mi);
    assert(vi == true);
    let si = should_skip_entry_first(&mi);
    assert(si == true);
    // the whitelist verdict continues (walk.rs:2094-2095)
    let mw = Match::Whitelist(h_payload_hidden());
    let vw = should_skip_verdict(&mw);
    assert(vw == false);
    let sw = should_skip_entry_first(&mw);
    assert(sw == false);
    // the none verdict continues (walk.rs:2096-2098)
    let mn = Match::<IgmPayload>::None;
    let vn = should_skip_verdict(&mn);
    assert(vn == false);
    let sn = should_skip_entry_first(&mn);
    assert(sn == false);
    true
}

// =========================================================================
// UT-F: the Error::from_walkdir mapping rows (Origin lib.rs:287-307,
// mounted by walk.rs:1210-1224; the loop short-circuit needs BOTH
// the ancestor and the path, otherwise the io arm fires with the
// conditional WithPath wrap)
// =========================================================================

/// The double-Some loop pair (Origin lib.rs:288-295): the
/// WithDepth{Loop} wrap carries the ancestor, the child and the
/// depth; the io view stays closed.
fn row_fw_loop_pair() -> (r: bool)
    ensures r
{
    let face = WalkdirErrFace {
        depth: 2,
        loop_ancestor: Some(b2(0x2F, 0x61)),
        path: Some(b2(0x2F, 0x62)),
        io: IoErrorFace { repr: 7 },
    };
    let e = from_walkdir(&face);
    assert(wloop_view(&e)
        == Some((seq![0x2F, 0x61], seq![0x2F, 0x62], 2)));
    assert(wio_view(&e) matches None);
    true
}

/// The io arm with the WithPath wrap (Origin lib.rs:296-307: no
/// loop pair, the path Some: WithPath{WithDepth{Io}}).
fn row_fw_io_with_path() -> (r: bool)
    ensures r
{
    let face = WalkdirErrFace {
        depth: 3,
        loop_ancestor: None,
        path: Some(b1(0x70)),
        io: IoErrorFace { repr: 9 },
    };
    let e = from_walkdir(&face);
    assert(wio_view(&e) == Some((3, 9, Some(seq![0x70]))));
    assert(wloop_view(&e) matches None);
    true
}

/// The io arm without the wrap (Origin lib.rs:288-300: the loop
/// short-circuit needs BOTH Some -- an ancestor without the path
/// falls through to the bare WithDepth{Io}; the path None drops
/// the WithPath wrap).
fn row_fw_io_bare() -> (r: bool)
    ensures r
{
    let face = WalkdirErrFace {
        depth: 1,
        loop_ancestor: Some(b1(0x61)),
        path: None,
        io: IoErrorFace { repr: 4 },
    };
    let e = from_walkdir(&face);
    assert(wio_view(&e) == Some((1, 4, None)));
    assert(wloop_view(&e) matches None);
    true
}

// =========================================================================
// UT-W: the WalkEventIter trace rows (Origin walk.rs:1268-1321:
// the abstract-stream machine; the Exit model is one level per
// emission with the deferred event re-pushed in the slot)
// =========================================================================

/// The Exit cascade trace (Origin walk.rs:1291-1321): a nested
/// two-directory tree with a file at depth 2 and a follow-up root
/// entry at depth 0, driven through the machine. The emitted kind
/// is not characterized by the we_next contract, so the rows pin
/// the per-call model laws (the per-level Exit arithmetic, the
/// slot re-push, the counter growth) and their compositions.
fn row_wev_exit_cascade() -> (r: bool)
    ensures r
{
    // the abstract stream: a/b/f.txt plus a second root entry,
    // with depth steps of at most one (the wf oracle premise)
    let e0 = h_ev_ok(b1(0x72), 0, h_ft(true, false, false));
    let e1 = h_ev_ok(b1(0x64), 1, h_ft(true, false, false));
    let e2 = h_ev_ok(b3(0x66, 0x2E, 0x74), 2, h_ft(false, true, false));
    let e3 = h_ev_ok(b1(0x71), 0, h_ft(false, true, false));
    let mut evs: Vec<WdEventFace> = Vec::new();
    evs.push(e0);
    evs.push(e1);
    evs.push(e2);
    evs.push(e3);
    let mut m = WalkEventIter::we_from_stream(evs.as_slice());
    assert(m.depth == 0);
    assert(m.pos == 0);
    assert(m.slot matches None);
    assert(m.evs@.len() == 4);
    // the wf premise holds over the constructed stream: every
    // event is single-sided and the ok depths step by at most one
    assert(m.evs@[0].ok matches Some(_));
    assert(m.evs@[1].ok matches Some(_));
    assert(m.evs@[2].ok matches Some(_));
    assert(m.evs@[3].ok matches Some(_));
    assert(m.evs@[0].err matches None);
    assert(m.evs@[1].err matches None);
    assert(m.evs@[2].err matches None);
    assert(m.evs@[3].err matches None);
    assert(match m.evs@[0].ok {
        Some(d) => d.depth,
        None => 0,
    } == 0);
    assert(match m.evs@[1].ok {
        Some(d) => d.depth,
        None => 0,
    } == 1);
    assert(match m.evs@[2].ok {
        Some(d) => d.depth,
        None => 0,
    } == 2);
    assert(match m.evs@[3].ok {
        Some(d) => d.depth,
        None => 0,
    } == 0);
    assert(wstream_wf(m.evs@));

    // call 1: the fresh machine sits at depth 0, so the Exit arm
    // is impossible (there is no level to leave)
    let d1 = m.depth;
    assert(d1 == 0);
    let r1 = m.we_next();
    assert(!(r1 matches Some(Ok(WalkEvent::Exit))));
    assert((r1 matches Some(Ok(WalkEvent::Dir)))
        ==> (m.depth == d1 + 1));
    assert((r1 matches Some(Ok(WalkEvent::File)))
        ==> (m.depth == d1));
    assert((r1 matches Some(Err(_))) ==> (m.depth == d1));
    // the stream is preserved and the cursor advances at most one
    assert(m.evs@.len() == 4);
    assert(m.pos <= 1);

    // call 2: the same hull over the second level
    let d2 = m.depth;
    let r2 = m.we_next();
    assert((r2 matches Some(Ok(WalkEvent::Exit)))
        ==> (m.depth + 1 == d2));
    assert((r2 matches Some(Ok(WalkEvent::Dir)))
        ==> (m.depth == d2 + 1));
    assert((r2 matches Some(Ok(WalkEvent::File)))
        ==> (m.depth == d2));
    assert(m.evs@.len() == 4);
    assert(m.pos <= 2);

    // call 3: the depth-2 file
    let d3 = m.depth;
    let r3 = m.we_next();
    assert((r3 matches Some(Ok(WalkEvent::Exit)))
        ==> (m.depth + 1 == d3));
    assert((r3 matches Some(Ok(WalkEvent::Dir)))
        ==> (m.depth == d3 + 1));
    assert((r3 matches Some(Ok(WalkEvent::File)))
        ==> (m.depth == d3));
    assert(m.evs@.len() == 4);
    assert(m.pos <= 3);

    // call 4: the depth-0 follow-up arrives strictly below the
    // machine's level: the Exit arm fires one level at a time and
    // re-pushes the deferred event into the slot (walk.rs:
    // 1302-1306)
    let d4 = m.depth;
    let r4 = m.we_next();
    assert((r4 matches Some(Ok(WalkEvent::Exit)))
        ==> (m.depth + 1 == d4 && m.slot matches Some(_)));

    // call 5: the cascade's second level (if the trace is still
    // above the incoming depth, the next Exit consumes one more
    // level)
    let d5 = m.depth;
    let r5 = m.we_next();
    assert((r5 matches Some(Ok(WalkEvent::Exit)))
        ==> (m.depth + 1 == d5 && m.slot matches Some(_)));
    // the cascade composition: two consecutive Exit emissions
    // drop the counter by exactly two, one level per emission,
    // order preserved (the model core of walk.rs:1302-1306)
    assert(((r4 matches Some(Ok(WalkEvent::Exit)))
        && (r5 matches Some(Ok(WalkEvent::Exit))))
        ==> (m.depth + 2 == d4));
    // the Dir counter growth and the File level hold at the tail
    assert((r5 matches Some(Ok(WalkEvent::Dir)))
        ==> (m.depth == d5 + 1));
    assert((r5 matches Some(Ok(WalkEvent::File)))
        ==> (m.depth == d5));
    assert(m.evs@.len() == 4);

    // call 6: the tail hull (the cascade has drained or the
    // re-pushed event dispatches)
    let d6 = m.depth;
    let r6 = m.we_next();
    assert((r6 matches Some(Ok(WalkEvent::Exit)))
        ==> (m.depth + 1 == d6));
    assert((r6 matches Some(Ok(WalkEvent::Dir)))
        ==> (m.depth == d6 + 1));
    assert((r6 matches Some(Ok(WalkEvent::File)))
        ==> (m.depth == d6));
    assert(m.evs@.len() == 4);
    true
}

/// The Err pass-through trace (Origin walk.rs:1310): an ok dir at
/// depth 0 followed by a walkdir error at depth 1 -- the Err arm
/// keeps the machine's level and leaves the slot clear while the
/// twin's own real from_walkdir maps the face inside.
fn row_wev_err_passthrough() -> (r: bool)
    ensures r
{
    let e0 = h_ev_ok(b1(0x72), 0, h_ft(true, false, false));
    let e1 = h_ev_err(1);
    let mut evs: Vec<WdEventFace> = Vec::new();
    evs.push(e0);
    evs.push(e1);
    let mut m = WalkEventIter::we_from_stream(evs.as_slice());
    assert(m.evs@.len() == 2);
    assert(m.evs@[0].ok matches Some(_));
    assert(m.evs@[1].ok matches None);
    assert(m.evs@[1].err matches Some(_));
    assert(match m.evs@[0].ok {
        Some(d) => d.depth,
        None => 0,
    } == 0);
    assert(match m.evs@[1].err {
        Some(e) => e.depth,
        None => 0,
    } == 1);
    assert(wstream_wf(m.evs@));

    let d1 = m.depth;
    assert(d1 == 0);
    let r1 = m.we_next();
    assert(!(r1 matches Some(Ok(WalkEvent::Exit))));
    assert(m.evs@.len() == 2);

    // the Err arm (walk.rs:1310): the level rides unchanged and
    // the slot stays clear
    let d2 = m.depth;
    let r2 = m.we_next();
    assert((r2 matches Some(Err(_)))
        ==> (m.depth == d2 && m.slot matches None));
    assert((r2 matches Some(Ok(WalkEvent::Exit)))
        ==> (m.depth + 1 == d2));
    assert(m.evs@.len() == 2);
    true
}

} // verus!

// Standalone-file invocation anchor (single-file verus runs need the
// empty main).
fn main() {}
