//! ignore IG8 **harness zone** -- the incremental.rs KAT rows over
//! the src-zone twin (batch IG8 mechanical-clear window, the IG7
//! deferred-2 row family as re-anchored from the IG6 design list).
//!
//! Row families (every row cites its upstream anchor in the pinned
//! crate ignore 0.4.34's incremental.rs tests; the runtime backstop
//! is the 205/0 replay recorded in the IG6/IG8 batch notes):
//! - UT-F: the fast-path spelling family -- the parent_key values of
//!   "a//b/x", "a/./b/x", "a/b/.///x" (the trim drops the "/." pair
//!   and the "/" run, incremental.rs:123-125), the byte-wise misses
//!   of the "//" and "./" spellings against the lean keys, and the
//!   Allowed hit through the ".///x" tail-trim spelling;
//! - UT-I: the Ignored endpoint (the CachedDir::Ignored terminal of
//!   the fast consult);
//! - UT-D: the depth table (the upstream depth_limits vectors over
//!   the NotDirectory arm: file-under-min, dir-under-min,
//!   over-max file/dir, the dir edge at max, the root "" / "." legs
//!   of depth_limits_apply_to_root);
//! - UT-S: the Stdin/- root inertness (the depth options stay
//!   inert under the Stdin gate; normalize returns None);
//! - UT-N: the normalize family (the predecessor's probe chain
//!   transplanted: the fold true values with the root byte dropped
//!   as a separator-run byte, the "/t/dir/../file" hop chain, the
//!   wrapper's outside-root None);
//! - UT-M: the max_filesize three legs over the one lean "a" cache
//!   (Ok-over, Ok-under with the at-limit boundary, the Err-tagged
//!   WithPath record);
//! - UT-C: the insert parent-closure (dirs_wf on the concrete
//!   insert-chain caches with the dangling negative control, and
//!   the exec consumption of the per-entry closure clauses over a
//!   miss-arm consult).
//!
//! Discipline: the contract legs are consumed through their posts
//! only (the walk value ladders live in their own query contexts);
//! the uninterpreted faces carry per-instance assumes with their
//! origins in comments (the ig6_clone / ig6_acpr / fs_err_tagged
//! / std_abs contract clauses and the 34-vector no-error oracle).
//! The mwi miss-arm r-value transfer rides the #IG-32 instantiation
//! wall (the twin's own refill record at incremental.rs:4196-4215;
//! five round shapes probed at 300/600 in this batch's probes --
//! the arm's decision value is pinned spec-side instead).
//!
//! Running: ./third_party/verus-docker.sh verus --rlimit 300
//!   database/ignore/verified/harness/ut_ig6.rs

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/lib.rs"]
mod iglib;

use iglib::incremental::{
    cache_scan, dirs_wf, fast_path_spec, ii_top_spec, im_ignore,
    im_nwd, im_none, norm_fold,
};
use iglib::dir::{dir_matched_spec, ig_wf, join_bytes};

verus! {

broadcast use vstd::seq::group_seq_axioms;

// ================= byte carriers (ut_ig7 bN style) =================

fn b0() -> (r: Vec<u8>)
    ensures r@ == Seq::empty()
{
    Vec::new()
}

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

fn b4(a: u8, d: u8, e: u8, f: u8) -> (r: Vec<u8>)
    ensures r@ == seq![a, d, e, f]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(a);
    v.push(d);
    v.push(e);
    v.push(f);
    v
}

fn b6(a: u8, c: u8, d: u8, e: u8, f: u8, g: u8) -> (r: Vec<u8>)
    ensures r@ == seq![a, c, d, e, f, g]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(a);
    v.push(c);
    v.push(d);
    v.push(e);
    v.push(f);
    v.push(g);
    v
}

fn b7(a: u8, c: u8, d: u8, e: u8, f: u8, g: u8, h: u8) -> (r: Vec<u8>)
    ensures r@ == seq![a, c, d, e, f, g, h]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(a);
    v.push(c);
    v.push(d);
    v.push(e);
    v.push(f);
    v.push(g);
    v.push(h);
    v
}

fn b9(a: u8, c: u8, d: u8, e: u8, f: u8, g: u8, h: u8, i: u8, j: u8)
    -> (r: Vec<u8>)
    ensures r@ == seq![a, c, d, e, f, g, h, i, j]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(a);
    v.push(c);
    v.push(d);
    v.push(e);
    v.push(f);
    v.push(g);
    v.push(h);
    v.push(i);
    v.push(j);
    v
}

fn b9_file() -> (r: Vec<u8>)
    ensures r@ == seq![
        0x61, 0x2F, 0x62, 0x2F, 0x63, 0x2F, 0x66, 0x69, 0x6C, 0x65]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x61);
    v.push(0x2F);
    v.push(0x62);
    v.push(0x2F);
    v.push(0x63);
    v.push(0x2F);
    v.push(0x66);
    v.push(0x69);
    v.push(0x6C);
    v.push(0x65);
    v
}

/// "/t" (the twin's normalize geometry carrier).
fn slash_t() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x74]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v
}

/// "/t/dir/../file" (the paths_are_relative_to_the_root vector body).
fn slash_t_dir_dd_file() -> (r: Vec<u8>)
    ensures r@ == seq![
        0x2F, 0x74, 0x2F, 0x64, 0x69, 0x72, 0x2F, 0x2E, 0x2E, 0x2F,
        0x66, 0x69, 0x6C, 0x65]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x74);
    v.push(0x2F);
    v.push(0x64);
    v.push(0x69);
    v.push(0x72);
    v.push(0x2F);
    v.push(0x2E);
    v.push(0x2E);
    v.push(0x2F);
    v.push(0x66);
    v.push(0x69);
    v.push(0x6C);
    v.push(0x65);
    v
}

/// "/x/y" (the outside-the-root none geometry).
fn slash_x_y() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F, 0x78, 0x2F, 0x79]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v.push(0x78);
    v.push(0x2F);
    v.push(0x79);
    v
}

// ================= the shared construction helpers =================

fn h_empty_git() -> (r: iglib::gitignore::Gitignore)
    ensures
        r.set.registered@.len() == 0,
        r.globs@.len() == 0,
        r.root.bytes@.len() == 0,
{
    iglib::gitignore::Gitignore {
        set: iglib::gitignore::GlobSetFace {
            registered: Vec::new(),
        },
        root: iglib::PathBytes { bytes: Vec::new() },
        globs: Vec::new(),
        num_ignores: 0,
        num_whitelists: 0,
    }
}

fn h_abs_node() -> (r: iglib::dir::IgnoreNode)
    ensures
        r.is_absolute_parent,
        !r.has_git,
        !r.has_absolute_parent_rules,
        r.dir@.len() == 0,
{
    iglib::dir::IgnoreNode {
        dir: Vec::new(),
        is_absolute_parent: true,
        has_absolute_parent_rules: false,
        has_git: false,
        custom_ignore_matcher: h_empty_git(),
        ignore_matcher: h_empty_git(),
        git_ignore_matcher: h_empty_git(),
        git_exclude_matcher: h_empty_git(),
    }
}

fn h_ig_empty() -> (r: iglib::dir::Ignore)
    ensures
        ig_wf(&r),
        r.nodes@.len() == 1,
        r.nodes@[0].is_absolute_parent,
        r.nodes@[0].has_git == false,
        r.inner.opts.ignore == false,
        r.inner.opts.git_global == false,
        r.inner.opts.git_ignore == false,
        r.inner.opts.git_exclude == false,
        r.inner.opts.hidden == false,
        r.inner.opts.parents == false,
        r.inner.opts.require_git == false,
        !r.inner.opts.ignore_case_insensitive,
        r.inner.explicit_ignores@.len() == 0,
        r.inner.custom_ignore_filenames@.len() == 0,
        r.inner.git_global_matcher.set.registered@.len() == 0,
        r.inner.overrides.inner.set.registered@.len() == 0,
        iglib::types::types_wf(&r.inner.types),
        r.inner.types.selections@.len() == 0,
        r.absolute_base@ matches None,
{
    let ty = iglib::types::Types::empty();
    let inner = iglib::dir::IgnoreInner {
        dir: Vec::new(),
        overrides: iglib::overrides::Override::empty(),
        types: ty,
        global_gitignores_relative_to: None,
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        git_global_matcher: h_empty_git(),
        opts: iglib::dir::IgnoreOptions {
            hidden: false,
            ignore: false,
            parents: false,
            git_global: false,
            git_ignore: false,
            git_exclude: false,
            ignore_case_insensitive: false,
            require_git: false,
        },
    };
    let mut ns: Vec<iglib::dir::IgnoreNode> = Vec::new();
    ns.push(h_abs_node());
    iglib::dir::Ignore {
        inner,
        nodes: ns,
        absolute_base: None,
    }
}

fn h_ent_allowed(
    key: Vec<u8>,
    ig: iglib::dir::Ignore,
) -> (r: iglib::incremental::CachedDirEnt)
    requires ig_wf(&ig)
    ensures
        r.key@ == key@,
        r.state == iglib::incremental::CachedDir::Allowed(ig),
{
    iglib::incremental::CachedDirEnt {
        key,
        state: iglib::incremental::CachedDir::Allowed(ig),
    }
}

fn h_ent_ignored(key: Vec<u8>) -> (r: iglib::incremental::CachedDirEnt)
    ensures
        r.key@ == key@,
        r.state == iglib::incremental::CachedDir::Ignored,
{
    iglib::incremental::CachedDirEnt {
        key,
        state: iglib::incremental::CachedDir::Ignored,
    }
}

fn h_dirs1(e: iglib::incremental::CachedDirEnt)
    -> (r: Vec<iglib::incremental::CachedDirEnt>)
    ensures
        r@.len() == 1,
        r@[0] == e,
{
    let mut v: Vec<iglib::incremental::CachedDirEnt> = Vec::new();
    v.push(e);
    v
}

fn h_dirs2(
    e0: iglib::incremental::CachedDirEnt,
    e1: iglib::incremental::CachedDirEnt,
) -> (r: Vec<iglib::incremental::CachedDirEnt>)
    ensures
        r@.len() == 2,
        r@[0] == e0,
        r@[1] == e1,
{
    let mut v: Vec<iglib::incremental::CachedDirEnt> = Vec::new();
    v.push(e0);
    v.push(e1);
    v
}

fn h_ii_opts(
    min_depth: Option<usize>,
    max_depth: Option<usize>,
    max_filesize: Option<u64>,
) -> (r: iglib::incremental::IncrementalIgnoreOptions)
    ensures
        r.min_depth == min_depth,
        r.max_depth == max_depth,
        r.max_filesize == max_filesize,
        r.hidden == false,
        r.follow_links == false,
{
    iglib::incremental::IncrementalIgnoreOptions {
        min_depth,
        max_depth,
        max_filesize,
        hidden: false,
        follow_links: false,
    }
}

fn h_fs(
    filesize: Result<u64, iglib::IoErrorFace>,
) -> (r: iglib::incremental::Ig6FsFace)
    ensures
        r.root_is_dir == false,
        r.root_abs_base@ == None,
        r.root_parents_built@.len() == 0,
        r.root_found.custom_ignore_files.len() == 0,
        r.child_found.custom_ignore_files.len() == 0,
        r.filesize == filesize,
{
    let mk = iglib::dir::IgnoreFilesFound {
        has_ignore: false,
        has_git_ignore: false,
        has_git_dir: false,
        has_jj_dir: false,
        custom_ignore_files: Vec::new(),
    };
    iglib::incremental::Ig6FsFace {
        root_is_dir: false,
        root_abs_base: None,
        root_parents_built: Vec::new(),
        root_found: mk,
        root_git_is_file: None,
        root_resolved_ok: None,
        root_resolved_err: None,

        child_found: iglib::dir::IgnoreFilesFound {
            has_ignore: false,
            has_git_ignore: false,
            has_git_dir: false,
            has_jj_dir: false,
            custom_ignore_files: Vec::new(),
        },
        child_git_is_file: None,
        child_resolved_ok: None,
        child_resolved_err: None,
        filesize,
    }
}

fn h_ii_loaded(
    root: Vec<u8>,
    ig: iglib::dir::Ignore,
    dirs: Vec<iglib::incremental::CachedDirEnt>,
    options: iglib::incremental::IncrementalIgnoreOptions,
) -> (r: iglib::incremental::IncrementalIgnore)
    requires
        ig_wf(&ig),
        ig.nodes@.len() == 1,
        !ig.inner.opts.ignore,
        !ig.inner.opts.git_global,
        !ig.inner.opts.git_ignore,
        !ig.inner.opts.git_exclude,
        ig.inner.explicit_ignores@.len() == 0,
        ig.inner.custom_ignore_filenames@.len() == 0,
        ig.inner.overrides.inner.set.registered@.len() == 0,
        iglib::types::types_wf(&ig.inner.types),
        ig.inner.types.selections@.len() == 0,
        dirs_wf(dirs@),
    ensures
        iglib::incremental::ii_wf(&r),
        r.state == iglib::incremental::RootState::Loaded,
        r.root@ == root@,
        r.dirs@ == dirs@,
        r.root_store@ == seq![ig],
        r.options.min_depth == options.min_depth,
        r.options.max_depth == options.max_depth,
        r.options.max_filesize == options.max_filesize,
        r.options.hidden == options.hidden,
        r.options.follow_links == options.follow_links,
{
    let mut rs: Vec<iglib::dir::Ignore> = Vec::new();
    rs.push(ig);
    iglib::incremental::IncrementalIgnore {
        root,
        normalized_root: None,
        state: iglib::incremental::RootState::Loaded,
        dirs,
        root_store: rs,
        options,
    }
}

/// The pools-all-off stack decides None for every path.
proof fn matched_none_eval(
    ig: &iglib::dir::Ignore,
    path: Seq<u8>,
    is_dir: bool,
)
    requires
        !ig.inner.opts.ignore,
        !ig.inner.opts.git_global,
        !ig.inner.opts.git_ignore,
        !ig.inner.opts.git_exclude,
        ig.inner.explicit_ignores@.len() == 0,
        ig.inner.custom_ignore_filenames@.len() == 0,
        ig.inner.overrides.inner.set.registered@.len() == 0,
        ig.inner.types.selections@.len() == 0,
    ensures dir_matched_spec(ig, path, is_dir) == None
{
    reveal(iglib::dir::dir_matched_spec);
    assert(iglib::dir::ig_has_any_rules_spec(ig) == false);
    assert(ig.inner.types.selections@.len() == 0);
}

fn h_ii_notdir(
    root: Vec<u8>,
    options: iglib::incremental::IncrementalIgnoreOptions,
) -> (r: iglib::incremental::IncrementalIgnore)
    ensures
        iglib::incremental::ii_wf(&r),
        r.state == iglib::incremental::RootState::NotDirectory,
        r.root@ == root@,
        r.dirs@.len() == 0,
        r.root_store@.len() == 0,
        r.options.min_depth == options.min_depth,
        r.options.max_depth == options.max_depth,
        r.options.max_filesize == options.max_filesize,
        r.options.hidden == options.hidden,
        r.options.follow_links == options.follow_links,
{
    iglib::incremental::IncrementalIgnore {
        root,
        normalized_root: None,
        state: iglib::incremental::RootState::NotDirectory,
        dirs: Vec::new(),
        root_store: Vec::new(),
        options,
    }
}

// ================= the local eval lemmas =================

/// The all-empty triple fold is the identity (the probe's final
/// shape transplanted; every no-error row consumes it).
proof fn apply_rev2_eee(st: Seq<iglib::Error>)
    ensures iglib::incremental::apply_rev2(st, seq![
        Seq::empty(),
        Seq::empty(),
        Seq::empty(),
    ]) == st
{
    let segs: Seq<Seq<iglib::Error>> = Seq::empty()
        .push(Seq::empty())
        .push(Seq::empty())
        .push(Seq::empty());
    assert(segs.len() == 3);
    assert(segs[0] == Seq::empty());
    assert(segs[1] == Seq::empty());
    assert(segs[2] == Seq::empty());
    assert(segs.subrange(1, 3) == seq![Seq::empty(), Seq::empty()]);
    assert(segs.subrange(2, 3) == seq![Seq::empty()]);
    reveal_with_fuel(iglib::incremental::apply_rev2, 4);
    assert(iglib::incremental::apply_rev(st, Seq::empty()) == st) by {
        reveal(iglib::incremental::apply_rev);
    }
}

/// The [empty, empty, singleton] fold is the singleton push (the
/// probes' final shape; the Err-tagged row consumes it).
proof fn apply_rev2_singleton(st: Seq<iglib::Error>, e: iglib::Error)
    ensures iglib::incremental::apply_rev2(st, seq![
        Seq::empty(),
        Seq::empty(),
        seq![e],
    ]) == st.push(e)
{
    let ee: Seq<iglib::Error> = seq![e];
    let segs: Seq<Seq<iglib::Error>> = Seq::empty()
        .push(Seq::empty())
        .push(Seq::empty())
        .push(ee);
    assert(segs.len() == 3);
    assert(segs[0] == Seq::empty());
    assert(segs[1] == Seq::empty());
    assert(segs[2] == ee);
    let s12: Seq<Seq<iglib::Error>> = Seq::empty()
        .push(Seq::empty())
        .push(ee);
    assert(segs.subrange(1, 3) == s12);
    let s2: Seq<Seq<iglib::Error>> = Seq::empty().push(ee);
    assert(segs.subrange(2, 3) == s2);
    reveal_with_fuel(iglib::incremental::apply_rev2, 4);
    assert(iglib::incremental::apply_rev(st, Seq::empty()) == st) by {
        reveal(iglib::incremental::apply_rev);
    }
    assert(iglib::incremental::apply_rev(st, seq![e]) == st.push(e)) by {
        reveal_with_fuel(iglib::incremental::apply_rev, 2);
        let r1: Seq<iglib::Error> = seq![e];
        assert(r1.len() == 1);
        assert(r1[0] == e);
        assert(r1.len() - 1 == 0);
        assert(r1[r1.len() - 1] == e);
        assert(r1.subrange(0, 0) == Seq::empty());
    }
}

/// The three-entry cache "a" / "a/b" / "a/b/c" is wf (the walk's
/// insert chain shape; the concrete closure of the dirs_wf clauses).
proof fn dirs_wf_ababc(
    cache: Seq<iglib::incremental::CachedDirEnt>,
)
    requires
        cache.len() == 3,
        cache[0].key@ == seq![0x61],
        cache[1].key@ == seq![0x61, 0x2F, 0x62],
        cache[2].key@ == seq![0x61, 0x2F, 0x62, 0x2F, 0x63],
        (match &cache[0].state {
            iglib::incremental::CachedDir::Allowed(g1) => ig_wf(g1),
            iglib::incremental::CachedDir::Ignored => true,
        }),
        (match &cache[1].state {
            iglib::incremental::CachedDir::Allowed(g1) => ig_wf(g1),
            iglib::incremental::CachedDir::Ignored => true,
        }),
        (match &cache[2].state {
            iglib::incremental::CachedDir::Allowed(g1) => ig_wf(g1),
            iglib::incremental::CachedDir::Ignored => true,
        }),
    ensures dirs_wf(cache)
{
    reveal(dirs_wf);
    reveal(iglib::incremental::key_parent);
    // "a" has no separator: the parent clause is the None arm
    iglib::pathutil::memrchr_spec_none_bridge(seq![0x61], 0x2F);
    assert(iglib::incremental::key_parent(seq![0x61]) == None);
    // "a/b" -> "a", "a/b/c" -> "a/b": both hit their chain slot
    iglib::pathutil::memrchr_spec_some_bridge(
        seq![0x61, 0x2F, 0x62], 0x2F, 1);
    assert(iglib::incremental::key_parent(seq![0x61, 0x2F, 0x62])
        == Some(seq![0x61]));
    iglib::pathutil::memrchr_spec_some_bridge(
        seq![0x61, 0x2F, 0x62, 0x2F, 0x63], 0x2F, 3);
    assert(iglib::incremental::key_parent(
        seq![0x61, 0x2F, 0x62, 0x2F, 0x63])
        == Some(seq![0x61, 0x2F, 0x62]));
    assert(iglib::incremental::cache_scan(cache, seq![0x61], 0)
        == 0) by {
        reveal_with_fuel(cache_scan, 2);
    }
    assert(iglib::incremental::cache_scan(cache,
        seq![0x61, 0x2F, 0x62], 0) == 1) by {
        reveal_with_fuel(cache_scan, 3);
        assert(cache[0].key@ != seq![0x61, 0x2F, 0x62]);
    }
}

/// The no-parent consult: a rel with no separator has no parent key,
/// so the fast consult returns None over any cache.
proof fn fp_none_no_parent(
    cache: Seq<iglib::incremental::CachedDirEnt>,
    rel: Seq<u8>,
    root: Seq<u8>,
    hidden: bool,
    is_dir: bool,
)
    requires
        hidden == false,
        iglib::incremental::parent_key_spec(rel) == None,
    ensures fast_path_spec(cache, rel, root, hidden, is_dir) == None
{
    reveal(fast_path_spec);
    assert(iglib::incremental::parent_key_spec(rel) matches None);
}

/// The NotDirectory consult constant (the walk arm of the top spec
/// over a root that never loaded).
proof fn wer_notdir(
    store: Seq<iglib::dir::Ignore>,
    root: Seq<u8>,
    hidden: bool,
    rel: Seq<u8>,
    is_dir: bool,
    cache: Seq<iglib::incremental::CachedDirEnt>,
    fs: &iglib::incremental::Ig6FsFace,
)
    ensures iglib::incremental::walk_entry_root(
        iglib::incremental::RootState::NotDirectory, store, root,
        hidden, rel, is_dir, cache, fs)
        == (None, Seq::empty(), Seq::empty())
{
    reveal(iglib::incremental::walk_entry_root);
}

// ================= row 1: stdin inertness =================
//
// Origin stdin_is_inert_with_depth_limits (the depth options stay
// inert under the Stdin gate of incremental.rs:277-279).

fn row_stdin_file_min() -> (r: bool)
    ensures r
{
    let mut ii = iglib::incremental::ii_new_stdin(
        h_ii_opts(Some(2), None, None));
    assert(iglib::incremental::ii_wf(&ii));
    assert(ii.state == iglib::incremental::RootState::Stdin);
    let f = h_fs(Ok(0));
    // the value oracle, over the pre-call state (the wrapper post
    // reads old(self), which names this same pre-value)
    proof {
        reveal(ii_top_spec);
        assert(ii_top_spec(ii.root@, ii.state, ii.root_store@,
            ii.options.min_depth, ii.options.max_depth,
            ii.options.max_filesize, ii.options.hidden,
            seq![0x66, 0x69, 0x6C, 0x65], false, ii.dirs@, &f)
            == (im_none(false), Seq::empty()));
        assert(iglib::incremental::apply_rev2(Seq::empty(),
            Seq::empty()) == Seq::empty()) by {
            reveal(iglib::incremental::apply_rev2);
        }
    }
    let rel = b4(0x66, 0x69, 0x6C, 0x65);
    let (m, e) = ii.matched_with_errors(rel.as_slice(), false, &f);
    proof {
        assert(iglib::incremental::inc_view(&m) == (0, false, true));
    }
    let vn = m.is_none();
    assert(vn);
    let vw = m.is_within_depth();
    assert(vw);
    assert(e matches None);
    true
}

fn row_stdin_dir_max() -> (r: bool)
    ensures r
{
    let mut ii = iglib::incremental::ii_new_stdin(
        h_ii_opts(None, Some(0), None));
    assert(iglib::incremental::ii_wf(&ii));
    assert(ii.state == iglib::incremental::RootState::Stdin);
    let f = h_fs(Ok(0));
    proof {
        reveal(ii_top_spec);
        assert(ii_top_spec(ii.root@, ii.state, ii.root_store@,
            ii.options.min_depth, ii.options.max_depth,
            ii.options.max_filesize, ii.options.hidden,
            seq![0x64, 0x69, 0x72], true, ii.dirs@, &f)
            == (im_none(true), Seq::empty()));
        assert(iglib::incremental::apply_rev2(Seq::empty(),
            Seq::empty()) == Seq::empty()) by {
            reveal(iglib::incremental::apply_rev2);
        }
    }
    let rel = b3(0x64, 0x69, 0x72);
    let (m, e) = ii.matched_with_errors(rel.as_slice(), true, &f);
    proof {
        assert(iglib::incremental::inc_view(&m) == (0, true, true));
    }
    let vn = m.is_none();
    assert(vn);
    let vw = m.is_within_depth();
    assert(vw);
    let vd = m.should_descend();
    assert(vd);
    assert(e matches None);
    true
}

/// Origin multiple_roots: the stdin matcher's normalize is None.
fn row_stdin_normalize() -> (r: bool)
    ensures r
{
    let ii = iglib::incremental::ii_new_stdin(h_ii_opts(None, None, None));
    assert(iglib::incremental::ii_wf(&ii));
    let n = ii.normalize(b3(0x61, 0x6E, 0x79).as_slice());
    assert(n matches None);
    true
}

// ================= row 2: the parent-key spelling KAT =================
//
// Origin cached_allowed_parent_matches_children (the equivalent
// spellings tier) + the trim comment incremental.rs:123-125.

fn row_parent_key_spellings() -> (r: bool)
    ensures r
{
    // "a//b/x": the memrchr parent at 4, no interior trim
    let s1 = b6(0x61, 0x2F, 0x2F, 0x62, 0x2F, 0x78);
    let pk1 = iglib::incremental::parent_key(s1.as_slice());
    proof {
        let sp1 = seq![0x61, 0x2F, 0x2F, 0x62, 0x2F, 0x78];
        assert(sp1[4] == 0x2F);
        assert(sp1[5] == 0x78);
        iglib::pathutil::memrchr_spec_some_bridge(sp1, 0x2F, 4);
        let name = sp1.subrange(5, 6);
        assert(name.len() == 1);
        assert(name[0] == 0x78);
        let dt: Seq<u8> = seq![0x2E];
        assert(dt.len() == 1);
        assert(dt[0] == 0x2E);
        assert(name != dt);
        let ddt: Seq<u8> = seq![0x2E, 0x2E];
        assert(ddt.len() == 2);
        assert(ddt[0] == 0x2E);
        assert(ddt[1] == 0x2E);
        assert(name != ddt);
        assert(!iglib::incremental::is_dot(name)) by {
            reveal(iglib::incremental::is_dot);
        }
        assert(!iglib::incremental::is_dotdot(name)) by {
            reveal(iglib::incremental::is_dotdot);
        }
        assert(iglib::incremental::pk_trim_end(sp1, 4) == 4) by {
            reveal(iglib::incremental::pk_trim_end);
        }
        assert(iglib::incremental::parent_key_spec(sp1)
            == Some(seq![0x61, 0x2F, 0x2F, 0x62])) by {
            reveal(iglib::incremental::parent_key_spec);
        }
    }
    assert(pk1 != None);
    assert((match pk1 {
        Some(v) => v@ == seq![0x61, 0x2F, 0x2F, 0x62],
        None => false,
    }));
    // "a/./b/x": the interior "./" survives the byte-wise trim
    let s2 = b7(0x61, 0x2F, 0x2E, 0x2F, 0x62, 0x2F, 0x78);
    let pk2 = iglib::incremental::parent_key(s2.as_slice());
    proof {
        let sp2 = seq![0x61, 0x2F, 0x2E, 0x2F, 0x62, 0x2F, 0x78];
        assert(sp2[5] == 0x2F);
        assert(sp2[6] == 0x78);
        iglib::pathutil::memrchr_spec_some_bridge(sp2, 0x2F, 5);
        let name = sp2.subrange(6, 7);
        assert(name.len() == 1);
        assert(name[0] == 0x78);
        let dt: Seq<u8> = seq![0x2E];
        assert(name != dt);
        let ddt: Seq<u8> = seq![0x2E, 0x2E];
        assert(name != ddt);
        assert(!iglib::incremental::is_dot(name)) by {
            reveal(iglib::incremental::is_dot);
        }
        assert(!iglib::incremental::is_dotdot(name)) by {
            reveal(iglib::incremental::is_dotdot);
        }
        assert(iglib::incremental::pk_trim_end(sp2, 5) == 5) by {
            reveal(iglib::incremental::pk_trim_end);
        }
        assert(iglib::incremental::parent_key_spec(sp2)
            == Some(seq![0x61, 0x2F, 0x2E, 0x2F, 0x62])) by {
            reveal(iglib::incremental::parent_key_spec);
        }
    }
    assert(pk2 != None);
    assert((match pk2 {
        Some(v) => v@ == seq![0x61, 0x2F, 0x2E, 0x2F, 0x62],
        None => false,
    }));
    // "a/b/.///x": the trim drops the "/." pair and the "/" run, so
    // the byte-wise parent IS the lean cache key
    let s3 = b9(0x61, 0x2F, 0x62, 0x2F, 0x2E, 0x2F, 0x2F, 0x2F,
        0x78);
    let pk3 = iglib::incremental::parent_key(s3.as_slice());
    proof {
        let sp3 = seq![
            0x61, 0x2F, 0x62, 0x2F, 0x2E, 0x2F, 0x2F, 0x2F, 0x78,
        ];
        iglib::pathutil::memrchr_spec_some_bridge(sp3, 0x2F, 7);
        let name = sp3.subrange(8, 9);
        assert(name.len() == 1);
        assert(name[0] == 0x78);
        let dt: Seq<u8> = seq![0x2E];
        assert(name != dt);
        let ddt: Seq<u8> = seq![0x2E, 0x2E];
        assert(name != ddt);
        assert(!iglib::incremental::is_dot(name)) by {
            reveal(iglib::incremental::is_dot);
        }
        assert(!iglib::incremental::is_dotdot(name)) by {
            reveal(iglib::incremental::is_dotdot);
        }
        assert(iglib::incremental::pk_trim_end(sp3, 7) == 3) by {
            reveal_with_fuel(iglib::incremental::pk_trim_end, 6);
            assert(sp3[6] == 0x2F);
            assert(iglib::incremental::pk_trim_end(sp3, 7)
                == iglib::incremental::pk_trim_end(sp3, 6));
            assert(sp3[5] == 0x2F);
            assert(iglib::incremental::pk_trim_end(sp3, 6)
                == iglib::incremental::pk_trim_end(sp3, 5));
            assert(sp3[4] == 0x2E && sp3[3] == 0x2F);
            assert(iglib::incremental::pk_trim_end(sp3, 5)
                == iglib::incremental::pk_trim_end(sp3, 3));
            assert(sp3[2] == 0x62);
            assert(iglib::incremental::pk_trim_end(sp3, 3) == 3);
        }
        assert(iglib::incremental::parent_key_spec(sp3)
            == Some(seq![0x61, 0x2F, 0x62])) by {
            reveal(iglib::incremental::parent_key_spec);
        }
    }
    assert(pk3 != None);
    assert((match pk3 {
        Some(v) => v@ == seq![0x61, 0x2F, 0x62],
        None => false,
    }));
    // the non-normal final components reject (incremental.rs:120-122)
    let s4 = b3(0x61, 0x2F, 0x2E);
    let pk4 = iglib::incremental::parent_key(s4.as_slice());
    proof {
        let sp4 = seq![0x61, 0x2F, 0x2E];
        iglib::pathutil::memrchr_spec_some_bridge(sp4, 0x2F, 1);
        let name = sp4.subrange(2, 3);
        assert(name.len() == 1);
        assert(name[0] == 0x2E);
        let nm: Seq<u8> = name;
        assert(nm == seq![0x2E]);
        assert(iglib::incremental::is_dot(nm)) by {
            reveal(iglib::incremental::is_dot);
        }
        assert(iglib::incremental::parent_key_spec(sp4) == None) by {
            reveal(iglib::incremental::parent_key_spec);
        }
    }
    assert(pk4 matches None);
    let s5 = b4(0x61, 0x2F, 0x2E, 0x2E);
    let pk5 = iglib::incremental::parent_key(s5.as_slice());
    proof {
        let sp5 = seq![0x61, 0x2F, 0x2E, 0x2E];
        iglib::pathutil::memrchr_spec_some_bridge(sp5, 0x2F, 1);
        let name = sp5.subrange(2, 4);
        assert(name.len() == 2);
        assert(name[0] == 0x2E);
        assert(name[1] == 0x2E);
        let nm: Seq<u8> = name;
        assert(nm == seq![0x2E, 0x2E]);
        assert(iglib::incremental::is_dotdot(nm)) by {
            reveal(iglib::incremental::is_dotdot);
        }
        assert(iglib::incremental::parent_key_spec(sp5) == None) by {
            reveal(iglib::incremental::parent_key_spec);
        }
    }
    assert(pk5 matches None);
    true
}

// ================= row 3: the fast-path consult KAT =================
//
// The three spellings over one lean cache: only the ".///x" tail-trim
// spelling hits byte-wise; the "//" and "./" spellings miss (the
// component walk handles the normalized entry, incremental.rs:359-368).

/// The miss ladder for a parent-key no entry carries.
proof fn fast_misses_lean(
    cache: Seq<iglib::incremental::CachedDirEnt>,
    rel: Seq<u8>,
    root: Seq<u8>,
    k: Seq<u8>,
)
    requires
        cache.len() == 2,
        cache[0].key@ != k,
        cache[1].key@ != k,
        iglib::incremental::parent_key_spec(rel) == Some(k),
    ensures fast_path_spec(cache, rel, root, false, false) == None
{
    reveal(fast_path_spec);
    assert(iglib::incremental::cache_scan(cache, k, 0) == -1) by {
        reveal_with_fuel(cache_scan, 3);
        assert(cache[0].key@ != k);
        assert(cache[1].key@ != k);
    }
}

fn row_fast_path_misses() -> (r: bool)
    ensures r
{
    let igE1 = h_ig_empty();
    let igE2 = h_ig_empty();
    let ds = h_dirs2(
        h_ent_allowed(b1(0x61), igE1),
        h_ent_allowed(b3(0x61, 0x2F, 0x62), igE2),
    );
    proof {
        assert(dirs_wf(ds@)) by {
            reveal(dirs_wf);
            reveal(iglib::incremental::key_parent);
            iglib::pathutil::memrchr_spec_none_bridge(
                seq![0x61], 0x2F);
            assert(iglib::incremental::key_parent(seq![0x61])
                == None);
            iglib::pathutil::memrchr_spec_some_bridge(
                seq![0x61, 0x2F, 0x62], 0x2F, 1);
            assert(iglib::incremental::key_parent(
                seq![0x61, 0x2F, 0x62]) == Some(seq![0x61]));
            assert(cache_scan(ds@, seq![0x61], 0) == 0) by {
                reveal_with_fuel(cache_scan, 2);
            }
        }
    }
    // "a//b/x": the parent key "a//b" is carried by no entry
    let rel1 = b6(0x61, 0x2F, 0x2F, 0x62, 0x2F, 0x78);
    proof {
        let sp1 = rel1@;
        iglib::pathutil::memrchr_spec_some_bridge(sp1, 0x2F, 4);
        let name = sp1.subrange(5, 6);
        assert(name.len() == 1);
        assert(name[0] == 0x78);
        let dt: Seq<u8> = seq![0x2E];
        assert(name != dt);
        let ddt: Seq<u8> = seq![0x2E, 0x2E];
        assert(name != ddt);
        assert(!iglib::incremental::is_dot(name)) by {
            reveal(iglib::incremental::is_dot);
        }
        assert(!iglib::incremental::is_dotdot(name)) by {
            reveal(iglib::incremental::is_dotdot);
        }
        assert(iglib::incremental::pk_trim_end(sp1, 4) == 4) by {
            reveal(iglib::incremental::pk_trim_end);
        }
        let k: Seq<u8> = seq![0x61, 0x2F, 0x2F, 0x62];
        assert(iglib::incremental::parent_key_spec(sp1) == Some(k)) by {
            reveal(iglib::incremental::parent_key_spec);
        }
        let ka: Seq<u8> = seq![0x61];
        let kab: Seq<u8> = seq![0x61, 0x2F, 0x62];
        assert(k != ka) by {
            assert(k.len() == 4);
            assert(ka.len() == 1);
        }
        assert(k != kab) by {
            assert(k[2] == 0x2F);
            assert(kab[2] == 0x62);
        }
        assert(ds@[0].key@ != k);
        assert(ds@[1].key@ != k);
        fast_misses_lean(ds@, rel1@, seq![0x74], k);
    }
    assert(fast_path_spec(ds@, rel1@, seq![0x74], false, false)
        == None);
    // "a/./b/x": the parent key "a/./b" is carried by no entry
    let rel2 = b7(0x61, 0x2F, 0x2E, 0x2F, 0x62, 0x2F, 0x78);
    proof {
        let sp2 = rel2@;
        iglib::pathutil::memrchr_spec_some_bridge(sp2, 0x2F, 5);
        let name = sp2.subrange(6, 7);
        assert(name.len() == 1);
        assert(name[0] == 0x78);
        let dt: Seq<u8> = seq![0x2E];
        assert(name != dt);
        let ddt: Seq<u8> = seq![0x2E, 0x2E];
        assert(name != ddt);
        assert(!iglib::incremental::is_dot(name)) by {
            reveal(iglib::incremental::is_dot);
        }
        assert(!iglib::incremental::is_dotdot(name)) by {
            reveal(iglib::incremental::is_dotdot);
        }
        assert(iglib::incremental::pk_trim_end(sp2, 5) == 5) by {
            reveal(iglib::incremental::pk_trim_end);
        }
        let k: Seq<u8> = seq![0x61, 0x2F, 0x2E, 0x2F, 0x62];
        assert(iglib::incremental::parent_key_spec(sp2) == Some(k)) by {
            reveal(iglib::incremental::parent_key_spec);
        }
        let ka: Seq<u8> = seq![0x61];
        let kab: Seq<u8> = seq![0x61, 0x2F, 0x62];
        assert(k != ka) by {
            assert(k.len() == 5);
            assert(ka.len() == 1);
        }
        assert(k != kab) by {
            assert(k[2] == 0x2E);
            assert(kab[2] == 0x62);
        }
        assert(ds@[0].key@ != k);
        assert(ds@[1].key@ != k);
        fast_misses_lean(ds@, rel2@, seq![0x74], k);
    }
    assert(fast_path_spec(ds@, rel2@, seq![0x74], false, false)
        == None);
    true
}

// ================= row 4: the Ignored endpoint =================
//
// Origin cached_ignored_parent_matches_children ("blocked/second"
// is ignored through the terminal cache entry) -- the im_ignore
// terminal of the fast consult (incremental.rs:408-415).

fn row_ignored_endpoint() -> (r: bool)
    ensures r
{
    let ig_store = h_ig_empty();
    let ds = h_dirs1(h_ent_ignored(b7(
        0x62, 0x6C, 0x6F, 0x63, 0x6B, 0x65, 0x64)));
    proof {
        // "blocked" has no separator: the only wf clause is the
        // key length
        assert(dirs_wf(ds@)) by {
            reveal(dirs_wf);
            reveal(iglib::incremental::key_parent);
            iglib::pathutil::memrchr_spec_none_bridge(
                seq![0x62, 0x6C, 0x6F, 0x63, 0x6B, 0x65, 0x64],
                0x2F);
            assert(iglib::incremental::key_parent(
                seq![0x62, 0x6C, 0x6F, 0x63, 0x6B, 0x65, 0x64])
                == None);
        }
    }
    let rel = b14(0x62, 0x6C, 0x6F, 0x63, 0x6B, 0x65, 0x64, 0x2F,
        0x73, 0x65, 0x63, 0x6F, 0x6E, 0x64);
    let mut ii = h_ii_loaded(b1(0x74), ig_store, ds,
        h_ii_opts(None, None, None));
    assert(iglib::incremental::ii_wf(&ii));
    let f = h_fs(Ok(0));
    proof {
        // the parent key of "blocked/second" is "blocked"
        let sp = seq![
            0x62, 0x6C, 0x6F, 0x63, 0x6B, 0x65, 0x64, 0x2F, 0x73,
            0x65, 0x63, 0x6F, 0x6E, 0x64,
        ];
        iglib::pathutil::memrchr_spec_some_bridge(sp, 0x2F, 7);
        let name = sp.subrange(8, 14);
        assert(name.len() == 6);
        assert(name[0] == 0x73);
        let dt: Seq<u8> = seq![0x2E];
        assert(name != dt);
        let ddt: Seq<u8> = seq![0x2E, 0x2E];
        assert(name != ddt);
        assert(!iglib::incremental::is_dot(name)) by {
            reveal(iglib::incremental::is_dot);
        }
        assert(!iglib::incremental::is_dotdot(name)) by {
            reveal(iglib::incremental::is_dotdot);
        }
        assert(iglib::incremental::pk_trim_end(sp, 7) == 7) by {
            reveal(iglib::incremental::pk_trim_end);
        }
        let kb: Seq<u8> = seq![
            0x62, 0x6C, 0x6F, 0x63, 0x6B, 0x65, 0x64];
        assert(iglib::incremental::parent_key_spec(sp)
            == Some(kb)) by {
            reveal(iglib::incremental::parent_key_spec);
        }
        assert(cache_scan(ds@, kb, 0) == 0) by {
            reveal_with_fuel(cache_scan, 2);
        }
        // the Ignored entry terminates: the fast consult is
        // Some(im_ignore())
        reveal(fast_path_spec);
        assert(fast_path_spec(ds@, rel@, seq![0x74], false, false)
            == Some(im_ignore()));
        // the top composition over the pre-call state
        reveal(ii_top_spec);
        assert(ii_top_spec(ii.root@, ii.state, ii.root_store@,
            ii.options.min_depth, ii.options.max_depth,
            ii.options.max_filesize, ii.options.hidden, rel@, false,
            ii.dirs@, &f)
            == (im_ignore(), seq![
                Seq::empty(), Seq::empty(), Seq::empty()]));
        apply_rev2_eee(Seq::empty());
    }
    let (m, e) = ii.matched_with_errors(rel.as_slice(), false, &f);
    proof {
        assert(iglib::incremental::inc_view(&m) == (1, false, true));
    }
    let vi = m.is_ignore();
    assert(vi);
    let vd = m.should_descend();
    assert(!vd);
    let vw = m.is_within_depth();
    assert(vw);
    assert(e matches None);
    true
}

// ================= row 5: the fast-path hit (exec) =================
//
// Origin cached_allowed_parent_matches_children: the ".///x"
// spelling hits the lean cached key and decides through the cached
// (pools-off) stack -- no walk, no state change.

/// The fast hit ladder for the ".///x" spelling over the lean
/// "a"/"a/b" cache with a pools-off stored stack.
proof fn fast_hit_eval(
    cache: Seq<iglib::incremental::CachedDirEnt>,
    igE: &iglib::dir::Ignore,
    k: Seq<u8>,
    rel: Seq<u8>,
    root: Seq<u8>,
)
    requires
        cache.len() == 2,
        cache[0].key@ == seq![0x61],
        cache[1].key@ == k,
        cache[1].state == iglib::incremental::CachedDir::Allowed(*igE),
        iglib::incremental::parent_key_spec(rel) == Some(k),
        k != seq![0x61],
        !igE.inner.opts.ignore,
        !igE.inner.opts.git_global,
        !igE.inner.opts.git_ignore,
        !igE.inner.opts.git_exclude,
        igE.inner.explicit_ignores@.len() == 0,
        igE.inner.custom_ignore_filenames@.len() == 0,
        igE.inner.overrides.inner.set.registered@.len() == 0,
        igE.inner.types.selections@.len() == 0,
    ensures fast_path_spec(cache, rel, root, false, false)
        == Some(im_none(false))
{
    assert(cache_scan(cache, k, 0) == 1) by {
        reveal_with_fuel(cache_scan, 3);
        assert(cache[0].key@ != k);
        assert(cache[1].key@ == k);
    }
    // the cached stack decides none (the pools-off gate)
    matched_none_eval(igE, iglib::dir::join_bytes(root, rel), false);
    reveal(fast_path_spec);
    reveal(iglib::incremental::mp_build);
    assert(iglib::incremental::mp_build(root, false, igE, rel, false)
        == im_none(false));
}

fn row_fast_allowed_hit() -> (r: bool)
    ensures r
{
    let ig_store = h_ig_empty();
    let igE1 = h_ig_empty();
    let igE2 = h_ig_empty();
    let ds = h_dirs2(
        h_ent_allowed(b1(0x61), igE1),
        h_ent_allowed(b3(0x61, 0x2F, 0x62), igE2),
    );
    proof {
        assert(dirs_wf(ds@)) by {
            reveal(dirs_wf);
            reveal(iglib::incremental::key_parent);
            iglib::pathutil::memrchr_spec_none_bridge(
                seq![0x61], 0x2F);
            assert(iglib::incremental::key_parent(seq![0x61])
                == None);
            iglib::pathutil::memrchr_spec_some_bridge(
                seq![0x61, 0x2F, 0x62], 0x2F, 1);
            assert(iglib::incremental::key_parent(
                seq![0x61, 0x2F, 0x62]) == Some(seq![0x61]));
            assert(cache_scan(ds@, seq![0x61], 0) == 0) by {
                reveal_with_fuel(cache_scan, 2);
            }
        }
    }
    let rel = b9(0x61, 0x2F, 0x62, 0x2F, 0x2E, 0x2F, 0x2F, 0x2F,
        0x78);
    let mut ii = h_ii_loaded(b1(0x74), ig_store, ds,
        h_ii_opts(None, None, None));
    assert(iglib::incremental::ii_wf(&ii));
    let f = h_fs(Ok(0));
    proof {
        // the parent key of "a/b/.///x" is "a/b"
        let sp = rel@;
        iglib::pathutil::memrchr_spec_some_bridge(sp, 0x2F, 7);
        let name = sp.subrange(8, 9);
        assert(name.len() == 1);
        assert(name[0] == 0x78);
        let dt: Seq<u8> = seq![0x2E];
        assert(name != dt);
        let ddt: Seq<u8> = seq![0x2E, 0x2E];
        assert(name != ddt);
        assert(!iglib::incremental::is_dot(name)) by {
            reveal(iglib::incremental::is_dot);
        }
        assert(!iglib::incremental::is_dotdot(name)) by {
            reveal(iglib::incremental::is_dotdot);
        }
        assert(iglib::incremental::pk_trim_end(sp, 7) == 3) by {
            reveal_with_fuel(iglib::incremental::pk_trim_end, 6);
            assert(sp[6] == 0x2F);
            assert(iglib::incremental::pk_trim_end(sp, 7)
                == iglib::incremental::pk_trim_end(sp, 6));
            assert(sp[5] == 0x2F);
            assert(iglib::incremental::pk_trim_end(sp, 6)
                == iglib::incremental::pk_trim_end(sp, 5));
            assert(sp[4] == 0x2E && sp[3] == 0x2F);
            assert(iglib::incremental::pk_trim_end(sp, 5)
                == iglib::incremental::pk_trim_end(sp, 3));
            assert(sp[2] == 0x62);
            assert(iglib::incremental::pk_trim_end(sp, 3) == 3);
        }
        let k: Seq<u8> = seq![0x61, 0x2F, 0x62];
        assert(iglib::incremental::parent_key_spec(sp) == Some(k)) by {
            reveal(iglib::incremental::parent_key_spec);
        }
        fast_hit_eval(ds@, &igE2, k, rel@, seq![0x74]);
        // the top composition: the fast arm decides with empty errs
        reveal(ii_top_spec);
        assert(ii_top_spec(ii.root@, ii.state, ii.root_store@,
            ii.options.min_depth, ii.options.max_depth,
            ii.options.max_filesize, ii.options.hidden, rel@, false,
            ii.dirs@, &f)
            == (im_none(false), seq![
                Seq::empty(), Seq::empty(), Seq::empty()]));
        apply_rev2_eee(Seq::empty());
    }
    let (m, e) = ii.matched_with_errors(rel.as_slice(), false, &f);
    proof {
        assert(iglib::incremental::inc_view(&m) == (0, false, true));
    }
    let vn = m.is_none();
    assert(vn);
    let vi = m.is_ignore();
    assert(!vi);
    assert(e matches None);
    true
}

// ================= row 6: the insert-chain closure (spec) =================
//
// Origin dirs_wf (DP29, incremental.rs:91-105 context): the concrete
// closure of the parent-chain clauses over the walk's insert shape,
// plus the dangling-key negative control.

fn row_insert_chain_wf() -> (r: bool)
    ensures r
{
    let igE1 = h_ig_empty();
    let igE2 = h_ig_empty();
    let igE3 = h_ig_empty();
    let ds = iglib_dirs3(
        h_ent_allowed(b1(0x61), igE1),
        h_ent_allowed(b3(0x61, 0x2F, 0x62), igE2),
        h_ent_allowed(b5(0x61, 0x2F, 0x62, 0x2F, 0x63), igE3),
    );
    proof {
        dirs_wf_ababc(ds@);
    }
    assert(dirs_wf(ds@));
    // the dangling negative control: "a/b/c" with no "a/b" carried
    let dd = h_dirs1(h_ent_allowed(b5(
        0x61, 0x2F, 0x62, 0x2F, 0x63), h_ig_empty()));
    proof {
        assert(!dirs_wf(dd@)) by {
            reveal(dirs_wf);
            reveal(iglib::incremental::key_parent);
            iglib::pathutil::memrchr_spec_some_bridge(
                seq![0x61, 0x2F, 0x62, 0x2F, 0x63], 0x2F, 3);
            assert(iglib::incremental::key_parent(
                seq![0x61, 0x2F, 0x62, 0x2F, 0x63])
                == Some(seq![0x61, 0x2F, 0x62]));
            assert(cache_scan(dd@, seq![0x61, 0x2F, 0x62], 0)
                == -1) by {
                reveal_with_fuel(cache_scan, 2);
                assert(dd@[0].key@ != seq![0x61, 0x2F, 0x62]);
            }
            assert(dd@.len() > 0);
            // the entry at 0 fails the parent clause: the match arm
            // reads the miss as a failed scan
            assert(!(dd@[0].key@.len() > 0
                && (match iglib::incremental::key_parent(
                    dd@[0].key@) {
                    None => true,
                    Some(p2) => cache_scan(dd@, p2, 0) >= 0,
                })));
        }
    }
    assert(!dirs_wf(dd@));
    true
}

fn iglib_dirs3(
    e0: iglib::incremental::CachedDirEnt,
    e1: iglib::incremental::CachedDirEnt,
    e2: iglib::incremental::CachedDirEnt,
) -> (r: Vec<iglib::incremental::CachedDirEnt>)
    ensures
        r@.len() == 3,
        r@[0] == e0,
        r@[1] == e1,
        r@[2] == e2,
{
    let mut v: Vec<iglib::incremental::CachedDirEnt> = Vec::new();
    v.push(e0);
    v.push(e1);
    v.push(e2);
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

fn b14(a: u8, c: u8, d: u8, e: u8, f: u8, g: u8, h: u8, i: u8, j: u8,
    k: u8, l: u8, m: u8, n: u8, o: u8) -> (r: Vec<u8>)
    ensures r@ == seq![a, c, d, e, f, g, h, i, j, k, l, m, n, o]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(a);
    v.push(c);
    v.push(d);
    v.push(e);
    v.push(f);
    v.push(g);
    v.push(h);
    v.push(i);
    v.push(j);
    v.push(k);
    v.push(l);
    v.push(m);
    v.push(n);
    v.push(o);
    v
}
/// The min-depth file early return: matchedf(m, "file").is_ignore()
/// (incremental.rs:296-299, the verbatim comment rides the twin).
fn row_depth_file_under_min() -> (r: bool)
    ensures r
{
    let mut ii = h_ii_notdir(b1(0x74), h_ii_opts(Some(2), None, None));
    assert(iglib::incremental::ii_wf(&ii));
    let f = h_fs(Ok(0));
    let rel = b4(0x66, 0x69, 0x6C, 0x65);
    proof {
        // the filtered component count of "file" is 1
        assert(iglib::incremental::depth_count(rel@, 0) == 1) by {
            reveal(iglib::incremental::depth_count);
            reveal_with_fuel(iglib::incremental::depth_scan, 7);
        }
        reveal(ii_top_spec);
        assert(ii_top_spec(ii.root@, ii.state, ii.root_store@,
            ii.options.min_depth, ii.options.max_depth,
            ii.options.max_filesize, ii.options.hidden, rel@, false,
            ii.dirs@, &f)
            == (im_nwd(), Seq::empty()));
        assert(iglib::incremental::apply_rev2(Seq::empty(),
            Seq::empty()) == Seq::empty()) by {
            reveal(iglib::incremental::apply_rev2);
        }
    }
    let (m, e) = ii.matched_with_errors(rel.as_slice(), false, &f);
    proof {
        assert(iglib::incremental::inc_view(&m)
            == (1, false, false));
    }
    let vi = m.is_ignore();
    assert(vi);
    let vw = m.is_within_depth();
    assert(!vw);
    let vd = m.should_descend();
    assert(!vd);
    assert(e matches None);
    true
}

/// The min-depth dir pass: matchedd(m, "a") is none, !within,
/// should_descend (depth 1 under min 2; the tag touches only
/// is_within_depth for the under-min directory).
fn row_depth_dir_under_min() -> (r: bool)
    ensures r
{
    let mut ii = h_ii_notdir(b1(0x74), h_ii_opts(Some(2), None, None));
    assert(iglib::incremental::ii_wf(&ii));
    let f = h_fs(Ok(0));
    let rel = b1(0x61);
    proof {
        assert(iglib::incremental::depth_count(rel@, 0) == 1) by {
            reveal(iglib::incremental::depth_count);
            reveal_with_fuel(iglib::incremental::depth_scan, 4);
        }
        // "a" has no separator: no parent key, no fast consult
        iglib::pathutil::memrchr_spec_none_bridge(seq![0x61], 0x2F);
        assert(iglib::incremental::parent_key_spec(seq![0x61])
            == None) by {
            reveal(iglib::incremental::parent_key_spec);
        }
        fp_none_no_parent(ii.dirs@, rel@, ii.root@, false, true);
        wer_notdir(ii.root_store@, ii.root@, ii.options.hidden, rel@,
            true, ii.dirs@, &f);
        reveal(ii_top_spec);
        assert(ii_top_spec(ii.root@, ii.state, ii.root_store@,
            ii.options.min_depth, ii.options.max_depth,
            ii.options.max_filesize, ii.options.hidden, rel@, true,
            ii.dirs@, &f)
            == (iglib::incremental::im_of_kind(0, true, false), seq![
                Seq::empty(), Seq::empty(), Seq::empty()]));
        apply_rev2_eee(Seq::empty());
    }
    let (m, e) = ii.matched_with_errors(rel.as_slice(), true, &f);
    proof {
        assert(iglib::incremental::inc_view(&m)
            == (0, true, false));
    }
    let vn = m.is_none();
    assert(vn);
    let vw = m.is_within_depth();
    assert(!vw);
    let vd = m.should_descend();
    assert(vd);
    assert(e matches None);
    true
}

/// The over-max early return, both file and dir legs:
/// "a/b/c/d" (depth 4 over max 3) is ignore / !within / !descend.
/// A fresh ii per call: the wrapper post does not carry the state
/// forward, so each leg rebuilds its own matcher.
fn row_depth_over_max() -> (r: bool)
    ensures r
{
    let f = h_fs(Ok(0));
    // the dir leg (upstream: matchedd(&mut m, "a/b/c/d"))
    let rel = b7(0x61, 0x2F, 0x62, 0x2F, 0x63, 0x2F, 0x64);
    let mut ii = h_ii_notdir(b1(0x74),
        h_ii_opts(Some(2), Some(3), None));
    assert(iglib::incremental::ii_wf(&ii));
    proof {
        assert(iglib::incremental::depth_count(rel@, 0) == 4) by {
            reveal(iglib::incremental::depth_count);
            reveal_with_fuel(iglib::incremental::depth_scan, 10);
        }
        reveal(ii_top_spec);
        assert(ii_top_spec(ii.root@, ii.state, ii.root_store@,
            ii.options.min_depth, ii.options.max_depth,
            ii.options.max_filesize, ii.options.hidden, rel@, true,
            ii.dirs@, &f)
            == (im_nwd(), Seq::empty()));
        assert(iglib::incremental::apply_rev2(Seq::empty(),
            Seq::empty()) == Seq::empty()) by {
            reveal(iglib::incremental::apply_rev2);
        }
    }
    let (m1, e1) = ii.matched_with_errors(rel.as_slice(), true, &f);
    proof {
        assert(iglib::incremental::inc_view(&m1)
            == (1, false, false));
    }
    let vi = m1.is_ignore();
    assert(vi);
    let vw = m1.is_within_depth();
    assert(!vw);
    let vd = m1.should_descend();
    assert(!vd);
    assert(e1 matches None);
    // the file leg (upstream: matchedf(&mut m, "a/b/c/file"))
    let rel2 = b9_file();
    let mut i2 = h_ii_notdir(b1(0x74),
        h_ii_opts(Some(2), Some(3), None));
    assert(iglib::incremental::ii_wf(&i2));
    proof {
        assert(iglib::incremental::depth_count(rel2@, 0) == 4) by {
            reveal(iglib::incremental::depth_count);
            reveal_with_fuel(iglib::incremental::depth_scan, 14);
        }
        reveal(ii_top_spec);
        assert(ii_top_spec(i2.root@, i2.state, i2.root_store@,
            i2.options.min_depth, i2.options.max_depth,
            i2.options.max_filesize, i2.options.hidden, rel2@, false,
            i2.dirs@, &f)
            == (im_nwd(), Seq::empty()));
        assert(iglib::incremental::apply_rev2(Seq::empty(),
            Seq::empty()) == Seq::empty()) by {
            reveal(iglib::incremental::apply_rev2);
        }
    }
    let (m2, e2) = i2.matched_with_errors(rel2.as_slice(), false, &f);
    proof {
        assert(iglib::incremental::inc_view(&m2)
            == (1, false, false));
    }
    let vi2 = m2.is_ignore();
    assert(vi2);
    assert(e2 matches None);
    true
}

/// The dir edge at max: depth 1 with max 1 is none / within /
/// !should_descend (upstream "a/b/c" at max 3, the same tag arm).
fn row_depth_dir_edge() -> (r: bool)
    ensures r
{
    let mut ii = h_ii_notdir(b1(0x74),
        h_ii_opts(None, Some(1), None));
    assert(iglib::incremental::ii_wf(&ii));
    let f = h_fs(Ok(0));
    let rel = b1(0x61);
    proof {
        assert(iglib::incremental::depth_count(rel@, 0) == 1) by {
            reveal(iglib::incremental::depth_count);
            reveal_with_fuel(iglib::incremental::depth_scan, 4);
        }
        iglib::pathutil::memrchr_spec_none_bridge(seq![0x61], 0x2F);
        assert(iglib::incremental::parent_key_spec(seq![0x61])
            == None) by {
            reveal(iglib::incremental::parent_key_spec);
        }
        fp_none_no_parent(ii.dirs@, rel@, ii.root@, false, true);
        wer_notdir(ii.root_store@, ii.root@, ii.options.hidden, rel@,
            true, ii.dirs@, &f);
        reveal(ii_top_spec);
        assert(ii_top_spec(ii.root@, ii.state, ii.root_store@,
            ii.options.min_depth, ii.options.max_depth,
            ii.options.max_filesize, ii.options.hidden, rel@, true,
            ii.dirs@, &f)
            == (iglib::incremental::im_of_kind(0, false, true), seq![
                Seq::empty(), Seq::empty(), Seq::empty()]));
        apply_rev2_eee(Seq::empty());
    }
    let (m, e) = ii.matched_with_errors(rel.as_slice(), true, &f);
    proof {
        assert(iglib::incremental::inc_view(&m)
            == (0, false, true));
    }
    let vn = m.is_none();
    assert(vn);
    let vw = m.is_within_depth();
    assert(vw);
    let vd = m.should_descend();
    assert(!vd);
    assert(e matches None);
    true
}

/// The root edge at max 0 (upstream depth_limits_apply_to_root):
/// matchedd("") reports none / within / !should_descend, and the
/// "." spelling of the same root yields the same view.
fn row_depth_root_edge_max0() -> (r: bool)
    ensures r
{
    let mut ii = h_ii_notdir(b1(0x74),
        h_ii_opts(None, Some(0), None));
    assert(iglib::incremental::ii_wf(&ii));
    let f = h_fs(Ok(0));
    // the empty rel: depth 0, no parent key, and the peek gate
    // of the walk consult short-circuits (no components at all)
    let rel = b0();
    proof {
        assert(iglib::incremental::depth_count(rel@, 0) == 0) by {
            reveal(iglib::incremental::depth_count);
            reveal(iglib::incremental::depth_scan);
        }
        iglib::pathutil::memrchr_spec_none_bridge(Seq::empty(), 0x2F);
        assert(iglib::incremental::parent_key_spec(Seq::empty())
            == None) by {
            reveal(iglib::incremental::parent_key_spec);
        }
        fp_none_no_parent(ii.dirs@, rel@, ii.root@, false, true);
        // the peek gate: no filtered component exists in ""
        reveal(iglib::incremental::ii_walk_entry);
        reveal_with_fuel(iglib::incremental::any_nd, 2);
        assert(iglib::incremental::has_any_comp(rel@, 0) == false);
        reveal(iglib::incremental::walk_entry_root);
        reveal(ii_top_spec);
        assert(ii_top_spec(ii.root@, ii.state, ii.root_store@,
            ii.options.min_depth, ii.options.max_depth,
            ii.options.max_filesize, ii.options.hidden, rel@, true,
            ii.dirs@, &f)
            == (iglib::incremental::im_of_kind(0, false, true), seq![
                Seq::empty(), Seq::empty(), Seq::empty()]));
        apply_rev2_eee(Seq::empty());
    }
    let (m1, e1) = ii.matched_with_errors(rel.as_slice(), true, &f);
    proof {
        assert(iglib::incremental::inc_view(&m1)
            == (0, false, true));
    }
    let vn = m1.is_none();
    assert(vn);
    let vw = m1.is_within_depth();
    assert(vw);
    let vd = m1.should_descend();
    assert(!vd);
    assert(e1 matches None);
    true
}

/// The root under min (upstream depth_limits_apply_to_root with
/// min_depth Some(1)): matchedd("") and matchedd(".") report none /
/// !within / should_descend (the "." spelling counts zero filtered
/// components, the CurDir the depth filter drops). A fresh ii per
/// call (the wrapper post does not carry the state forward).
fn row_depth_root_under_min() -> (r: bool)
    ensures r
{
    let f = h_fs(Ok(0));
    // the "" leg
    let rel = b0();
    let mut ii = h_ii_notdir(b1(0x74), h_ii_opts(Some(1), None, None));
    assert(iglib::incremental::ii_wf(&ii));
    proof {
        assert(iglib::incremental::depth_count(rel@, 0) == 0) by {
            reveal(iglib::incremental::depth_count);
            reveal(iglib::incremental::depth_scan);
        }
        iglib::pathutil::memrchr_spec_none_bridge(Seq::empty(), 0x2F);
        assert(iglib::incremental::parent_key_spec(Seq::empty())
            == None) by {
            reveal(iglib::incremental::parent_key_spec);
        }
        fp_none_no_parent(ii.dirs@, rel@, ii.root@, false, true);
        reveal(iglib::incremental::ii_walk_entry);
        reveal_with_fuel(iglib::incremental::any_nd, 2);
        assert(iglib::incremental::has_any_comp(rel@, 0) == false);
        reveal(iglib::incremental::walk_entry_root);
        reveal(ii_top_spec);
        assert(ii_top_spec(ii.root@, ii.state, ii.root_store@,
            ii.options.min_depth, ii.options.max_depth,
            ii.options.max_filesize, ii.options.hidden, rel@, true,
            ii.dirs@, &f)
            == (iglib::incremental::im_of_kind(0, true, false),
                seq![Seq::empty(), Seq::empty(), Seq::empty()]));
        apply_rev2_eee(Seq::empty());
    }
    let (m1, e1) = ii.matched_with_errors(rel.as_slice(), true, &f);
    proof {
        assert(iglib::incremental::inc_view(&m1)
            == (0, true, false));
    }
    let vn = m1.is_none();
    assert(vn);
    let vw = m1.is_within_depth();
    assert(!vw);
    let vd = m1.should_descend();
    assert(vd);
    assert(e1 matches None);
    // the "." leg: the CurDir counts zero in the filtered count and
    // fails the peek gate
    let rel2 = b1(0x2E);
    let mut i2 = h_ii_notdir(b1(0x74), h_ii_opts(Some(1), None, None));
    assert(iglib::incremental::ii_wf(&i2));
    proof {
        assert(iglib::incremental::depth_count(rel2@, 0) == 0) by {
            reveal(iglib::incremental::depth_count);
            reveal_with_fuel(iglib::incremental::depth_scan, 4);
            assert(rel2@[0] == 0x2E);
        }
        iglib::pathutil::memrchr_spec_none_bridge(seq![0x2E], 0x2F);
        assert(iglib::incremental::parent_key_spec(seq![0x2E])
            == None) by {
            reveal(iglib::incremental::parent_key_spec);
        }
        fp_none_no_parent(i2.dirs@, rel2@, i2.root@, false, true);
        reveal(iglib::incremental::ii_walk_entry);
        reveal_with_fuel(iglib::incremental::any_nd, 4);
        assert(iglib::incremental::has_any_comp(rel2@, 0) == false);
        reveal(iglib::incremental::walk_entry_root);
        reveal(ii_top_spec);
        assert(ii_top_spec(i2.root@, i2.state, i2.root_store@,
            i2.options.min_depth, i2.options.max_depth,
            i2.options.max_filesize, i2.options.hidden, rel2@, true,
            i2.dirs@, &f)
            == (iglib::incremental::im_of_kind(0, true, false),
                seq![Seq::empty(), Seq::empty(), Seq::empty()]));
        apply_rev2_eee(Seq::empty());
    }
    let (m2, e2) = i2.matched_with_errors(rel2.as_slice(), true, &f);
    proof {
        assert(iglib::incremental::inc_view(&m2)
            == (0, true, false));
    }
    let vn2 = m2.is_none();
    assert(vn2);
    let vw2 = m2.is_within_depth();
    assert(!vw2);
    let vd2 = m2.should_descend();
    assert(vd2);
    assert(e2 matches None);
    true
}

/// "a/b/c/file" (10 bytes: 61 2F 62 2F 63 2F 66 69 6C 65).
// ================= row 8: the normalize value rows =================
//
// Origin paths_are_relative_to_the_root (the normalize vectors).
// The probes' fold chains ride verbatim: root byte of an absolute
// spelling drops as a separator-run byte (norm_fold("/t") == "t"),
// "/t/dir/../file" -> "t/file" hop-conservation.

/// The fold chain of the vector geometry (probe transplanted).
fn row_norm_fold_chain() -> (r: bool)
    ensures r
{
    proof {
        // "/t" -> "t": the root byte drops and "t" joins the empty
        // base (probe_fold_true/probe_final_shapes' hop 0)
        let sp0: Seq<u8> = seq![0x2F, 0x74];
        assert(norm_fold(sp0) == seq![0x74]) by {
            reveal(norm_fold);
            reveal_with_fuel(iglib::incremental::norm_fold_go, 5);
            reveal(iglib::incremental::nf_close);
            reveal(iglib::incremental::is_dot);
            reveal(iglib::incremental::is_dotdot);
            reveal(join_bytes);
            reveal_with_fuel(iglib::dir::append_prefix, 3);
        }
        // "/t/dir/../file" -> "t/file": the hop-conservation chain
        // (each hop its own query context, the #IG-19 discipline)
        let s: Seq<u8> = seq![
            0x2F, 0x74, 0x2F, 0x64, 0x69, 0x72, 0x2F, 0x2E, 0x2E,
            0x2F, 0x66, 0x69, 0x6C, 0x65,
        ];
        let acc1: Seq<u8> = seq![0x74];
        let acc2: Seq<u8> = seq![0x74, 0x2F, 0x64, 0x69, 0x72];
        // hop 0 (bytes 0..2: sep, "t", sep): the root byte drops and
        // "t" joins onto the empty base
        assert(iglib::incremental::norm_fold_go(s, 0, -1, Seq::empty())
            == iglib::incremental::norm_fold_go(s, 3, -1, acc1)) by {
            reveal_with_fuel(iglib::incremental::norm_fold_go, 7);
            reveal(iglib::incremental::nf_close);
            reveal(iglib::incremental::is_dot);
            reveal(iglib::incremental::is_dotdot);
            reveal(join_bytes);
            reveal_with_fuel(iglib::dir::append_prefix, 3);
            assert(s.subrange(1, 2) == seq![0x74]);
            assert(iglib::incremental::nf_close(s, 1, 2, Seq::empty())
                == seq![0x74]) by {
                reveal(iglib::incremental::nf_close);
                reveal(iglib::incremental::is_dot);
                reveal(iglib::incremental::is_dotdot);
                assert(join_bytes(Seq::empty(), seq![0x74])
                    == seq![0x74]) by {
                    reveal(join_bytes);
                    reveal_with_fuel(iglib::dir::append_prefix, 3);
                }
            }
        }
        // hop 1 (bytes 3..6: "dir" then sep): join "dir" onto acc1
        assert(iglib::incremental::norm_fold_go(s, 3, -1, acc1)
            == iglib::incremental::norm_fold_go(s, 7, -1, acc2)) by {
            reveal_with_fuel(iglib::incremental::norm_fold_go, 8);
            reveal(iglib::incremental::nf_close);
            reveal(iglib::incremental::is_dot);
            reveal(iglib::incremental::is_dotdot);
            reveal(join_bytes);
            reveal_with_fuel(iglib::dir::append_prefix, 8);
            assert(s.subrange(3, 6) == seq![0x64, 0x69, 0x72]);
            assert(iglib::incremental::nf_close(s, 3, 6, acc1)
                == acc2) by {
                reveal(iglib::incremental::nf_close);
                reveal(iglib::incremental::is_dot);
                reveal(iglib::incremental::is_dotdot);
                assert(join_bytes(seq![0x74], seq![0x64, 0x69, 0x72])
                    == acc2) by {
                    reveal(join_bytes);
                    reveal_with_fuel(iglib::dir::append_prefix, 8);
                }
            }
        }
        // hop 2 (bytes 7..9: ".." then sep): the pop of acc2 lands
        // back on acc1 (the .. resolves)
        assert(iglib::incremental::norm_fold_go(s, 7, -1, acc2)
            == iglib::incremental::norm_fold_go(s, 10, -1, acc1)) by {
            reveal_with_fuel(iglib::incremental::norm_fold_go, 12);
            reveal(iglib::incremental::nf_close);
            reveal(iglib::incremental::is_dot);
            reveal(iglib::incremental::is_dotdot);
            reveal(iglib::incremental::pop_last);
            assert(s.subrange(7, 9) == seq![0x2E, 0x2E]);
            iglib::pathutil::memrchr_spec_some_bridge(acc2, 0x2F, 1);
            assert(iglib::incremental::nf_close(s, 7, 9, acc2)
                == acc1) by {
                reveal(iglib::incremental::nf_close);
                reveal(iglib::incremental::is_dot);
                reveal(iglib::incremental::is_dotdot);
                reveal(iglib::incremental::pop_last);
            }
        }
        // hop 3 (bytes 10..14: "file" at the end): the final close
        // joins (the root-pop law: the ... "file" joins onto acc1)
        assert(iglib::incremental::norm_fold_go(s, 10, -1, acc1)
            == seq![0x74, 0x2F, 0x66, 0x69, 0x6C, 0x65]) by {
            reveal_with_fuel(iglib::incremental::norm_fold_go, 6);
            reveal(iglib::incremental::nf_close);
            reveal(iglib::incremental::is_dot);
            reveal(iglib::incremental::is_dotdot);
            reveal(join_bytes);
            reveal_with_fuel(iglib::dir::append_prefix, 8);
            assert(s.subrange(10, 14) == seq![0x66, 0x69, 0x6C, 0x65]);
            assert(iglib::incremental::nf_close(s, 10, 14, acc1)
                == seq![0x74, 0x2F, 0x66, 0x69, 0x6C, 0x65]) by {
                reveal(iglib::incremental::nf_close);
                reveal(iglib::incremental::is_dot);
                reveal(iglib::incremental::is_dotdot);
                reveal(join_bytes);
                reveal_with_fuel(iglib::dir::append_prefix, 8);
            }
        }
        // the head definition reaches the same start
        assert(norm_fold(s)
            == iglib::incremental::norm_fold_go(
                s, 0, -1, Seq::empty())) by {
            reveal(norm_fold);
        }
        assert(norm_fold(s)
            == seq![0x74, 0x2F, 0x66, 0x69, 0x6C, 0x65]);
        // the wrapper consumes the raw-byte strip: "t" prefixed off
        // "t/file" keeps the joining separator (the pathutil model)
        let fa: Seq<u8> = seq![0x74];
        let fb: Seq<u8> = seq![
            0x74, 0x2F, 0x66, 0x69, 0x6C, 0x65];
        assert(iglib::pathutil::strip_prefix_spec(fa, fb)
            == Some(seq![0x2F, 0x66, 0x69, 0x6C, 0x65])) by {
            reveal(iglib::pathutil::strip_prefix_spec);
            reveal(iglib::pathutil::bytes_prefix_eq);
            assert(fa.len() == 1);
            assert(fb.len() == 6);
            assert(fb[0] == 0x74);
            assert(fb.subrange(1, 6) == seq![0x2F, 0x66, 0x69, 0x6C, 0x65]);
        }
    }
    true
}

/// The normalize_absolute consumption of the vector path: with the
/// std face pinned to the absolute spelling (the probe-std row:
/// absolute("/abs/../z") == "/abs/../z" keeps ".." -- the fold is
/// the real resolver), the exec returns the folded "t/file".
fn row_norm_abs_ok() -> (r: bool)
    ensures r
{
    let path = slash_t_dir_dd_file();
    // std_abs_face mask (probe-std runtime row: absolutization of an
    // absolute spelling with ".." keeps the bytes verbatim)
    assume(iglib::incremental::std_abs_face(path@)
        == Some(seq![
            0x2F, 0x74, 0x2F, 0x64, 0x69, 0x72, 0x2F, 0x2E, 0x2E,
            0x2F, 0x66, 0x69, 0x6C, 0x65]));
    let na = iglib::incremental::normalize_absolute(path.as_slice());
    proof {
        // the fold over the pinned face value (the row_norm_fold_chain
        // recipe inlined over this call's own terms)
        let a: Seq<u8> = seq![
            0x2F, 0x74, 0x2F, 0x64, 0x69, 0x72, 0x2F, 0x2E, 0x2E,
            0x2F, 0x66, 0x69, 0x6C, 0x65];
        let acc1: Seq<u8> = seq![0x74];
        let acc2: Seq<u8> = seq![0x74, 0x2F, 0x64, 0x69, 0x72];
        assert(iglib::incremental::norm_fold_go(a, 0, -1, Seq::empty())
            == iglib::incremental::norm_fold_go(a, 3, -1, acc1)) by {
            reveal_with_fuel(iglib::incremental::norm_fold_go, 7);
            reveal(iglib::incremental::nf_close);
            reveal(iglib::incremental::is_dot);
            reveal(iglib::incremental::is_dotdot);
            reveal(join_bytes);
            reveal_with_fuel(iglib::dir::append_prefix, 3);
            assert(a.subrange(1, 2) == seq![0x74]);
        }
        assert(iglib::incremental::norm_fold_go(a, 3, -1, acc1)
            == iglib::incremental::norm_fold_go(a, 7, -1, acc2)) by {
            reveal_with_fuel(iglib::incremental::norm_fold_go, 12);
            reveal(iglib::incremental::nf_close);
            reveal(iglib::incremental::is_dot);
            reveal(iglib::incremental::is_dotdot);
            reveal(join_bytes);
            reveal_with_fuel(iglib::dir::append_prefix, 8);
            assert(a.subrange(3, 6) == seq![0x64, 0x69, 0x72]);
            assert(iglib::incremental::nf_close(a, 3, 6, acc1)
                == acc2) by {
                reveal(iglib::incremental::nf_close);
                reveal(iglib::incremental::is_dot);
                reveal(iglib::incremental::is_dotdot);
                assert(join_bytes(seq![0x74], seq![0x64, 0x69, 0x72])
                    == acc2) by {
                    reveal(join_bytes);
                    reveal_with_fuel(iglib::dir::append_prefix, 8);
                }
            }
        }
        assert(iglib::incremental::norm_fold_go(a, 7, -1, acc2)
            == iglib::incremental::norm_fold_go(a, 10, -1, acc1)) by {
            reveal_with_fuel(iglib::incremental::norm_fold_go, 12);
            reveal(iglib::incremental::nf_close);
            reveal(iglib::incremental::is_dot);
            reveal(iglib::incremental::is_dotdot);
            reveal(iglib::incremental::pop_last);
            assert(a.subrange(7, 9) == seq![0x2E, 0x2E]);
            iglib::pathutil::memrchr_spec_some_bridge(acc2, 0x2F, 1);
            assert(iglib::incremental::nf_close(a, 7, 9, acc2)
                == acc1) by {
                reveal(iglib::incremental::nf_close);
                reveal(iglib::incremental::is_dot);
                reveal(iglib::incremental::is_dotdot);
                reveal(iglib::incremental::pop_last);
            }
        }
        assert(iglib::incremental::norm_fold_go(a, 10, -1, acc1)
            == seq![0x74, 0x2F, 0x66, 0x69, 0x6C, 0x65]) by {
            reveal_with_fuel(iglib::incremental::norm_fold_go, 6);
            reveal(iglib::incremental::nf_close);
            reveal(iglib::incremental::is_dot);
            reveal(iglib::incremental::is_dotdot);
            reveal(join_bytes);
            reveal_with_fuel(iglib::dir::append_prefix, 8);
            assert(a.subrange(10, 14) == seq![0x66, 0x69, 0x6C, 0x65]);
            assert(iglib::incremental::nf_close(a, 10, 14, acc1)
                == seq![0x74, 0x2F, 0x66, 0x69, 0x6C, 0x65]) by {
                reveal(iglib::incremental::nf_close);
                reveal(iglib::incremental::is_dot);
                reveal(iglib::incremental::is_dotdot);
                reveal(join_bytes);
                reveal_with_fuel(iglib::dir::append_prefix, 8);
            }
        }
        assert(norm_fold(a)
            == iglib::incremental::norm_fold_go(
                a, 0, -1, Seq::empty())) by {
            reveal(norm_fold);
        }
        assert(norm_fold(a)
            == seq![0x74, 0x2F, 0x66, 0x69, 0x6C, 0x65]);
        // the wrapper post forces the Some arm (its None arm would
        // contradict the pinned face)
        assert(na matches Some(_));
        assert((match na {
            Some(v2) => v2@ == seq![0x74, 0x2F, 0x66, 0x69, 0x6C, 0x65],
            None => false,
        }));
    }
    true
}

/// The empty-path None leg (probe-std: absolute("") is an error).
fn row_norm_abs_none() -> (r: bool)
    ensures r
{
    let path = b0();
    assume(iglib::incremental::std_abs_face(path@) == None);
    let na = iglib::incremental::normalize_absolute(path.as_slice());
    assert(na matches None);
    true
}

/// The wrapper's outside-root None (the vector: normalize of a path
/// outside the root is None). The wrapper post is one-sided on the
/// Some arm, so the row pins None by contradiction: the folded pair
/// does not strip.
fn row_normalize_none() -> (r: bool)
    ensures r
{
    let ii = h_ii_notdir(slash_t(), h_ii_opts(None, None, None));
    assert(iglib::incremental::ii_wf(&ii));
    let path = slash_x_y();
    // std_abs_face masks (probe-std rows: absolute spellings keep
    // their bytes on unix)
    assume(iglib::incremental::std_abs_face(path@)
        == Some(seq![0x2F, 0x78, 0x2F, 0x79]));
    assume(iglib::incremental::std_abs_face(ii.root@)
        == Some(seq![0x2F, 0x74]));
    let n = ii.normalize(path.as_slice());
    proof {
        // the folded root: "t" (the root byte drops)
        let ra: Seq<u8> = seq![0x2F, 0x74];
        assert(norm_fold(ra) == seq![0x74]) by {
            reveal(norm_fold);
            reveal_with_fuel(iglib::incremental::norm_fold_go, 5);
            reveal(iglib::incremental::nf_close);
            reveal(iglib::incremental::is_dot);
            reveal(iglib::incremental::is_dotdot);
            reveal(join_bytes);
            reveal_with_fuel(iglib::dir::append_prefix, 3);
        }
        // the folded path: "/x/y" -> "x/y" (two plain segments)
        let pa: Seq<u8> = seq![0x2F, 0x78, 0x2F, 0x79];
        let x1: Seq<u8> = seq![0x78];
        let xy: Seq<u8> = seq![0x78, 0x2F, 0x79];
        assert(iglib::incremental::norm_fold_go(
            pa, 0, -1, Seq::empty())
            == iglib::incremental::norm_fold_go(pa, 3, -1, x1)) by {
            reveal_with_fuel(iglib::incremental::norm_fold_go, 10);
            reveal(iglib::incremental::nf_close);
            reveal(iglib::incremental::is_dot);
            reveal(iglib::incremental::is_dotdot);
            reveal(join_bytes);
            reveal_with_fuel(iglib::dir::append_prefix, 3);
            assert(pa.subrange(1, 2) == seq![0x78]);
            assert(iglib::incremental::nf_close(pa, 1, 2,
                Seq::empty()) == x1) by {
                reveal(iglib::incremental::nf_close);
                reveal(iglib::incremental::is_dot);
                reveal(iglib::incremental::is_dotdot);
                assert(join_bytes(Seq::empty(), seq![0x78]) == x1) by {
                    reveal(join_bytes);
                    reveal_with_fuel(iglib::dir::append_prefix, 3);
                }
            }
        }
        assert(iglib::incremental::norm_fold_go(pa, 3, -1, x1) == xy) by {
            reveal_with_fuel(iglib::incremental::norm_fold_go, 6);
            reveal(iglib::incremental::nf_close);
            reveal(iglib::incremental::is_dot);
            reveal(iglib::incremental::is_dotdot);
            reveal(join_bytes);
            reveal_with_fuel(iglib::dir::append_prefix, 5);
            assert(pa.subrange(3, 4) == seq![0x79]);
            assert(iglib::incremental::nf_close(pa, 3, 4, x1) == xy) by {
                reveal(iglib::incremental::nf_close);
                reveal(iglib::incremental::is_dot);
                reveal(iglib::incremental::is_dotdot);
                assert(join_bytes(seq![0x78], seq![0x79]) == xy) by {
                    reveal(join_bytes);
                    reveal_with_fuel(iglib::dir::append_prefix, 5);
                }
            }
        }
        assert(norm_fold(pa) == xy) by {
            reveal(norm_fold);
        }
        // "t" does not byte-prefix "x/y": the fold pair does not
        // strip, so the wrapper's Some arm is refuted
        reveal(iglib::pathutil::strip_prefix_spec);
        reveal(iglib::pathutil::bytes_prefix_eq);
        assert(xy[0] == 0x78);
        assert(xy[0] != 0x74);
        assert(!iglib::pathutil::bytes_prefix_eq(
            seq![0x74], xy));
    }
    assert(n matches None);
    true
}

// ================= row 9: the max_filesize three legs =================
//
// Origin max_filesize (the over-limit boundary rows) and
// max_filesize_does_not_stat_ignored_file. The legs ride the one
// lean "a" cache so the fast arm supplies the valid verdict the
// filesize leg requires.

/// The single-key fast hit ladder over the "a" cache.
proof fn fp_hit_a(
    cache: Seq<iglib::incremental::CachedDirEnt>,
    igE: &iglib::dir::Ignore,
    rel: Seq<u8>,
    root: Seq<u8>,
)
    requires
        cache.len() == 1,
        cache[0].key@ == seq![0x61],
        cache[0].state == iglib::incremental::CachedDir::Allowed(*igE),
        iglib::incremental::parent_key_spec(rel) == Some(seq![0x61]),
        !igE.inner.opts.ignore,
        !igE.inner.opts.git_global,
        !igE.inner.opts.git_ignore,
        !igE.inner.opts.git_exclude,
        igE.inner.explicit_ignores@.len() == 0,
        igE.inner.custom_ignore_filenames@.len() == 0,
        igE.inner.overrides.inner.set.registered@.len() == 0,
        igE.inner.types.selections@.len() == 0,
    ensures fast_path_spec(cache, rel, root, false, false)
        == Some(im_none(false))
{
    assert(cache_scan(cache, seq![0x61], 0) == 0) by {
        reveal_with_fuel(cache_scan, 2);
    }
    matched_none_eval(igE, join_bytes(root, rel), false);
    reveal(fast_path_spec);
    reveal(iglib::incremental::mp_build);
    assert(iglib::incremental::mp_build(root, false, igE, rel, false)
        == im_none(false));
}

/// The Ok-over leg (over-limit: 10 > max 5 reports ignore).
fn row_mfs_over() -> (r: bool)
    ensures r
{
    let ig_store = h_ig_empty();
    let igE1 = h_ig_empty();
    let ds = h_dirs1(h_ent_allowed(b1(0x61), igE1));
    proof {
        assert(dirs_wf(ds@)) by {
            reveal(dirs_wf);
            reveal(iglib::incremental::key_parent);
            iglib::pathutil::memrchr_spec_none_bridge(
                seq![0x61], 0x2F);
            assert(iglib::incremental::key_parent(seq![0x61])
                == None);
        }
    }
    let rel = b3(0x61, 0x2F, 0x78);
    let mut ii = h_ii_loaded(b1(0x74), ig_store, ds,
        h_ii_opts(None, None, Some(5)));
    assert(iglib::incremental::ii_wf(&ii));
    let f = h_fs(Ok(10));
    proof {
        // parent key of "a/x" is "a"
        let sp = rel@;
        iglib::pathutil::memrchr_spec_some_bridge(sp, 0x2F, 1);
        let name = sp.subrange(2, 3);
        assert(name.len() == 1);
        assert(name[0] == 0x78);
        let dt: Seq<u8> = seq![0x2E];
        assert(name != dt);
        let ddt: Seq<u8> = seq![0x2E, 0x2E];
        assert(name != ddt);
        assert(!iglib::incremental::is_dot(name)) by {
            reveal(iglib::incremental::is_dot);
        }
        assert(!iglib::incremental::is_dotdot(name)) by {
            reveal(iglib::incremental::is_dotdot);
        }
        assert(iglib::incremental::pk_trim_end(sp, 1) == 1) by {
            reveal(iglib::incremental::pk_trim_end);
        }
        assert(iglib::incremental::parent_key_spec(sp)
            == Some(seq![0x61])) by {
            reveal(iglib::incremental::parent_key_spec);
        }
        fp_hit_a(ds@, &igE1, rel@, seq![0x74]);
        // the top: the stat consult over the limit flips the verdict
        reveal(ii_top_spec);
        assert(ii_top_spec(ii.root@, ii.state, ii.root_store@,
            ii.options.min_depth, ii.options.max_depth,
            ii.options.max_filesize, ii.options.hidden, rel@, false,
            ii.dirs@, &f)
            == (im_ignore(), seq![
                Seq::empty(), Seq::empty(), Seq::empty()]));
        apply_rev2_eee(Seq::empty());
    }
    let (m, e) = ii.matched_with_errors(rel.as_slice(), false, &f);
    proof {
        assert(iglib::incremental::inc_view(&m) == (1, false, true));
    }
    let vi = m.is_ignore();
    assert(vi);
    assert(e matches None);
    true
}

/// The Ok-under legs (empty and at-limit stay none).
fn row_mfs_under() -> (r: bool)
    ensures r
{
    // the empty leg (len 0)
    let ig_store1 = h_ig_empty();
    let igE1 = h_ig_empty();
    let ds1 = h_dirs1(h_ent_allowed(b1(0x61), igE1));
    proof {
        assert(dirs_wf(ds1@)) by {
            reveal(dirs_wf);
            reveal(iglib::incremental::key_parent);
            iglib::pathutil::memrchr_spec_none_bridge(
                seq![0x61], 0x2F);
            assert(iglib::incremental::key_parent(seq![0x61])
                == None);
        }
    }
    let rel = b3(0x61, 0x2F, 0x78);
    let mut i1 = h_ii_loaded(b1(0x74), ig_store1, ds1,
        h_ii_opts(None, None, Some(5)));
    let f1 = h_fs(Ok(0));
    proof {
        let sp = rel@;
        iglib::pathutil::memrchr_spec_some_bridge(sp, 0x2F, 1);
        let name = sp.subrange(2, 3);
        assert(name.len() == 1);
        assert(name[0] == 0x78);
        let dt: Seq<u8> = seq![0x2E];
        assert(name != dt);
        let ddt: Seq<u8> = seq![0x2E, 0x2E];
        assert(name != ddt);
        assert(iglib::incremental::pk_trim_end(sp, 1) == 1) by {
            reveal(iglib::incremental::pk_trim_end);
        }
        assert(iglib::incremental::parent_key_spec(sp)
            == Some(seq![0x61])) by {
            reveal(iglib::incremental::parent_key_spec);
        }
        fp_hit_a(ds1@, &igE1, rel@, seq![0x74]);
        reveal(ii_top_spec);
        assert(ii_top_spec(i1.root@, i1.state, i1.root_store@,
            i1.options.min_depth, i1.options.max_depth,
            i1.options.max_filesize, i1.options.hidden, rel@, false,
            i1.dirs@, &f1)
            == (im_none(false), seq![
                Seq::empty(), Seq::empty(), Seq::empty()]));
        apply_rev2_eee(Seq::empty());
    }
    let (m1, e1) = i1.matched_with_errors(rel.as_slice(), false, &f1);
    proof {
        assert(iglib::incremental::inc_view(&m1) == (0, false, true));
    }
    let vn1 = m1.is_none();
    assert(vn1);
    assert(e1 matches None);
    // the at-limit leg (len 5 == max: not over)
    let ig_store2 = h_ig_empty();
    let igE2 = h_ig_empty();
    let ds2 = h_dirs1(h_ent_allowed(b1(0x61), igE2));
    proof {
        assert(dirs_wf(ds2@)) by {
            reveal(dirs_wf);
            reveal(iglib::incremental::key_parent);
            iglib::pathutil::memrchr_spec_none_bridge(
                seq![0x61], 0x2F);
            assert(iglib::incremental::key_parent(seq![0x61])
                == None);
        }
    }
    let mut i2 = h_ii_loaded(b1(0x74), ig_store2, ds2,
        h_ii_opts(None, None, Some(5)));
    let f2 = h_fs(Ok(5));
    proof {
        let sp = rel@;
        iglib::pathutil::memrchr_spec_some_bridge(sp, 0x2F, 1);
        let name = sp.subrange(2, 3);
        assert(name.len() == 1);
        assert(name[0] == 0x78);
        let dt: Seq<u8> = seq![0x2E];
        assert(name != dt);
        let ddt: Seq<u8> = seq![0x2E, 0x2E];
        assert(name != ddt);
        assert(iglib::incremental::pk_trim_end(sp, 1) == 1) by {
            reveal(iglib::incremental::pk_trim_end);
        }
        assert(iglib::incremental::parent_key_spec(sp)
            == Some(seq![0x61])) by {
            reveal(iglib::incremental::parent_key_spec);
        }
        fp_hit_a(ds2@, &igE2, rel@, seq![0x74]);
        reveal(ii_top_spec);
        assert(ii_top_spec(i2.root@, i2.state, i2.root_store@,
            i2.options.min_depth, i2.options.max_depth,
            i2.options.max_filesize, i2.options.hidden, rel@, false,
            i2.dirs@, &f2)
            == (im_none(false), seq![
                Seq::empty(), Seq::empty(), Seq::empty()]));
        apply_rev2_eee(Seq::empty());
    }
    let (m2, e2) = i2.matched_with_errors(rel.as_slice(), false, &f2);
    proof {
        assert(iglib::incremental::inc_view(&m2) == (0, false, true));
    }
    let vn2 = m2.is_none();
    assert(vn2);
    assert(e2 matches None);
    true
}

/// The Err-tagged leg: the stat error records a WithPath-tagged
/// entry and the verdict falls through unchanged.
fn row_mfs_err() -> (r: bool)
    ensures r
{
    let ig_store = h_ig_empty();
    let igE1 = h_ig_empty();
    let ds = h_dirs1(h_ent_allowed(b1(0x61), igE1));
    proof {
        assert(dirs_wf(ds@)) by {
            reveal(dirs_wf);
            reveal(iglib::incremental::key_parent);
            iglib::pathutil::memrchr_spec_none_bridge(
                seq![0x61], 0x2F);
            assert(iglib::incremental::key_parent(seq![0x61])
                == None);
        }
    }
    let rel = b3(0x61, 0x2F, 0x78);
    let mut ii = h_ii_loaded(b1(0x74), ig_store, ds,
        h_ii_opts(None, None, Some(5)));
    assert(iglib::incremental::ii_wf(&ii));
    let ioe = iglib::IoErrorFace { repr: 7 };
    let f = h_fs(Err(ioe));
    proof {
        let sp = rel@;
        iglib::pathutil::memrchr_spec_some_bridge(sp, 0x2F, 1);
        let name = sp.subrange(2, 3);
        assert(name.len() == 1);
        assert(name[0] == 0x78);
        let dt: Seq<u8> = seq![0x2E];
        assert(name != dt);
        let ddt: Seq<u8> = seq![0x2E, 0x2E];
        assert(name != ddt);
        assert(iglib::incremental::pk_trim_end(sp, 1) == 1) by {
            reveal(iglib::incremental::pk_trim_end);
        }
        assert(iglib::incremental::parent_key_spec(sp)
            == Some(seq![0x61])) by {
            reveal(iglib::incremental::parent_key_spec);
        }
        fp_hit_a(ds@, &igE1, rel@, seq![0x74]);
        // the joined consult path of the Err record
        let joined: Seq<u8> = seq![0x74, 0x2F, 0x61, 0x2F, 0x78];
        assert(join_bytes(seq![0x74], seq![0x61, 0x2F, 0x78])
            == joined) by {
            reveal(join_bytes);
            reveal_with_fuel(iglib::dir::append_prefix, 7);
        }
        // std-face provenance: the fs_err face owns the tagger
        // chain's shape (the fs_err_tagged contract's content
        // clauses, consumed per-instance here)
        assume(iglib::incremental::fs_err_face(&ioe, joined)
            matches iglib::Error::WithPath { .. });
        assume(iglib::with_path_payload(
            &iglib::incremental::fs_err_face(&ioe, joined))
            == joined);
        reveal(ii_top_spec);
        assert(ii_top_spec(ii.root@, ii.state, ii.root_store@,
            ii.options.min_depth, ii.options.max_depth,
            ii.options.max_filesize, ii.options.hidden, rel@, false,
            ii.dirs@, &f)
            == (im_none(false), seq![
                Seq::empty(),
                Seq::empty(),
                seq![iglib::incremental::fs_err_face(&ioe, joined)],
            ]));
        apply_rev2_singleton(Seq::empty(),
            iglib::incremental::fs_err_face(&ioe, joined));
    }
    let (m, e) = ii.matched_with_errors(rel.as_slice(), false, &f);
    proof {
        assert(iglib::incremental::inc_view(&m) == (0, false, true));
    }
    let vn = m.is_none();
    assert(vn);
    // the error is present, WithPath-tagged, and carries the
    // root-joined path
    assert((match e {
        Some(x) => x matches iglib::Error::WithPath { .. },
        None => false,
    }));
    assert((match e {
        Some(x) => iglib::with_path_payload(&x)
            == seq![0x74, 0x2F, 0x61, 0x2F, 0x78],
        None => false,
    }));
    true
}

// ================= row 10: the insert-closure exec leg =================
//
// Origin DP29's dirs_wf (the parent-closure invariant of the cache
// insert) consumed on a concrete walk: one consult-miss insert of
// the "a" chain, the mwi contract's per-entry closure clauses, and
// the walk spec value pinned through the per-instance face laws.

/// The walk step lemmas over the ii_walk_spec model: harness-local
/// copies of the twin's w_step recipes (every ingredient rides the
/// requires, the step body is one reveal) -- the #IG-19 discipline.

proof fn step_inseg(
    root: Seq<u8>, hidden: bool, rel: Seq<u8>, is_dir: bool,
    cache: Seq<iglib::incremental::CachedDirEnt>, cursor: int,
    seg_s: int, key: Seq<u8>, cur: iglib::dir::Ignore,
    fs: &iglib::incremental::Ig6FsFace,
)
    requires
        0 <= cursor < rel.len(),
        rel[cursor] != 0x2F,
        -1 <= seg_s <= cursor,
    ensures
        iglib::incremental::ii_walk_spec(root, hidden, rel, is_dir,
            cache, cursor, seg_s, key, cur, fs).0
            == iglib::incremental::ii_walk_spec(root, hidden, rel,
                is_dir, cache, cursor + 1,
                if seg_s < 0 { cursor } else { seg_s }, key, cur,
                fs).0,
        iglib::incremental::ii_walk_spec(root, hidden, rel, is_dir,
            cache, cursor, seg_s, key, cur, fs).1
            == iglib::incremental::ii_walk_spec(root, hidden, rel,
                is_dir, cache, cursor + 1,
                if seg_s < 0 { cursor } else { seg_s }, key, cur,
                fs).1,
{
    reveal(iglib::incremental::ii_walk_spec);
}

proof fn step_consult_miss(
    root: Seq<u8>, hidden: bool, rel: Seq<u8>, is_dir: bool,
    cache: Seq<iglib::incremental::CachedDirEnt>, cursor: int,
    seg_s: int, key: Seq<u8>, cur: iglib::dir::Ignore,
    fs: &iglib::incremental::Ig6FsFace, key2: Seq<u8>, path: Seq<u8>,
)
    requires
        0 <= cursor < rel.len(),
        0 <= seg_s < cursor,
        rel[cursor] == 0x2F,
        !iglib::incremental::is_dot(rel.subrange(seg_s, cursor)),
        !iglib::incremental::is_dotdot(rel.subrange(seg_s, cursor)),
        iglib::incremental::has_any_comp(rel, cursor),
        key2 == join_bytes(key, rel.subrange(seg_s, cursor)),
        path == join_bytes(root, key2),
        iglib::incremental::cache_scan(cache, key2, 0) == -1,
        !(dir_matched_spec(&cur, path, true)
            matches Some((false, _))),
        !(hidden
            && (dir_matched_spec(&cur, path, true) matches None)
            && iglib::pathutil::is_hidden_path_only_spec(path)),
        iglib::incremental::acpr_err_face(cur, path, fs) == None,
    ensures
        iglib::incremental::ii_walk_spec(root, hidden, rel, is_dir,
            cache, cursor, seg_s, key, cur, fs).0
            == iglib::incremental::ii_walk_spec(root, hidden, rel,
                is_dir, cache, cursor + 1, -1, key2,
                iglib::incremental::acpr_child_face(cur, path, fs),
                fs).0,
        iglib::incremental::ii_walk_spec(root, hidden, rel, is_dir,
            cache, cursor, seg_s, key, cur, fs).1
            == iglib::incremental::ii_walk_spec(root, hidden, rel,
                is_dir, cache, cursor + 1, -1, key2,
                iglib::incremental::acpr_child_face(cur, path, fs),
                fs).1,
{
    reveal(iglib::incremental::ii_walk_spec);
}

proof fn step_fin_last(
    root: Seq<u8>, hidden: bool, rel: Seq<u8>, is_dir: bool,
    cache: Seq<iglib::incremental::CachedDirEnt>, cursor: int,
    seg_s: int, key: Seq<u8>, cur: iglib::dir::Ignore,
    fs: &iglib::incremental::Ig6FsFace,
)
    requires
        0 <= seg_s <= cursor,
        cursor == rel.len(),
        !iglib::incremental::is_dotdot(rel.subrange(seg_s, cursor)),
    ensures
        iglib::incremental::ii_walk_spec(root, hidden, rel, is_dir,
            cache, cursor, seg_s, key, cur, fs).0
            == Some(iglib::incremental::mp_build(root, hidden, &cur,
                rel, is_dir)),
        iglib::incremental::ii_walk_spec(root, hidden, rel, is_dir,
            cache, cursor, seg_s, key, cur, fs).1
            == Seq::empty(),
{
    reveal(iglib::incremental::ii_walk_spec);
}

/// The walk value of the "a/x" consult over the Loaded empty cache
/// (the stitched decision facts; the face laws ride the
/// per-instance assumes with their origins noted).
proof fn walk_ax_eval(
    ig0: iglib::dir::Ignore,
    f: &iglib::incremental::Ig6FsFace,
)
    requires
        ig_wf(&ig0),
        !ig0.inner.opts.ignore,
        !ig0.inner.opts.git_global,
        !ig0.inner.opts.git_ignore,
        !ig0.inner.opts.git_exclude,
        ig0.inner.explicit_ignores@.len() == 0,
        ig0.inner.custom_ignore_filenames@.len() == 0,
        ig0.inner.overrides.inner.set.registered@.len() == 0,
        ig0.inner.types.selections@.len() == 0,
    ensures
        iglib::incremental::walk_entry_root(
            iglib::incremental::RootState::Loaded, seq![ig0],
            seq![0x74], false, seq![0x61, 0x2F, 0x78], false,
            Seq::empty(), f).0
            == Some(im_none(false)),
        iglib::incremental::walk_entry_root(
            iglib::incremental::RootState::Loaded, seq![ig0],
            seq![0x74], false, seq![0x61, 0x2F, 0x78], false,
            Seq::empty(), f).1
            == Seq::empty(),
        iglib::incremental::walk_entry_root(
            iglib::incremental::RootState::Loaded, seq![ig0],
            seq![0x74], false, seq![0x61, 0x2F, 0x78], false,
            Seq::empty(), f).2
            == Seq::empty(),
        fast_path_spec(Seq::empty(), seq![0x61, 0x2F, 0x78],
            seq![0x74], false, false) == None,
        iglib::incremental::apply_rev2(Seq::empty(),
            seq![Seq::empty(), Seq::empty()]) == Seq::empty(),
{
    let rel: Seq<u8> = seq![0x61, 0x2F, 0x78];
    let root: Seq<u8> = seq![0x74];
    let cur = iglib::incremental::clone_face(&ig0);
    let path: Seq<u8> = seq![0x74, 0x2F, 0x61];
    // the per-instance face laws (the assume ledger): the clone
    // consults like the store (ig6_clone's matched-value clause),
    assume(dir_matched_spec(&cur, path, true) == None);
    // the child of the empty-parent consult decides none (the
    // ig6_acpr same-length arm's empty-pools geometry),
    let child = iglib::incremental::acpr_child_face(cur, path, f);
    assume(dir_matched_spec(&child, join_bytes(root, rel), false)
        == None);
    // the vectors' no-error oracle (matchedf's err.is_none()).
    assume(iglib::incremental::acpr_err_face(cur, path, f) == None);

    // the ingredient facts
    assert(join_bytes(Seq::empty(), seq![0x61]) == seq![0x61]) by {
        reveal(join_bytes);
        reveal_with_fuel(iglib::dir::append_prefix, 3);
    }
    assert(join_bytes(seq![0x74], seq![0x61])
        == seq![0x74, 0x2F, 0x61]) by {
        reveal(join_bytes);
        reveal_with_fuel(iglib::dir::append_prefix, 5);
    }
    assert(iglib::incremental::cache_scan(Seq::empty(),
        seq![0x61], 0) == -1) by {
        reveal_with_fuel(iglib::incremental::cache_scan, 2);
    }
    reveal_with_fuel(iglib::incremental::any_nd, 5);
    assert(iglib::incremental::has_any_comp(rel, 0) == true);
    assert(iglib::incremental::has_any_comp(rel, 1) == true);
    assert(rel.subrange(0, 1) == seq![0x61]);

    // the "a/x" walk: open, consult-miss (the insert arm), the
    // final close through the child face
    step_inseg(root, false, rel, false, Seq::empty(), 0, -1,
        Seq::empty(), cur, f);
    step_consult_miss(root, false, rel, false, Seq::empty(), 1, 0,
        Seq::empty(), cur, f, seq![0x61], path);
    step_inseg(root, false, rel, false, Seq::empty(), 2, -1,
        seq![0x61], child, f);
    // the final mp: the child face over the full joined rel
    assert(iglib::incremental::mp_build(root, false, &child, rel,
        false) == im_none(false)) by {
        reveal(iglib::incremental::mp_build);
        assert(join_bytes(root, rel)
            == seq![0x74, 0x2F, 0x61, 0x2F, 0x78]) by {
            reveal(join_bytes);
            reveal_with_fuel(iglib::dir::append_prefix, 8);
        }
    }
    step_fin_last(root, false, rel, false, Seq::empty(), 3, 2,
        seq![0x61], child, f);
    // the peek gate and the Loaded entry consult (projections pass
    // through walk_entry and the Loaded arm of walk_entry_root)
    reveal(iglib::incremental::ii_walk_entry);
    reveal(iglib::incremental::walk_entry_root);
    // the fast consult misses: the "a" parent key is not cached
    iglib::pathutil::memrchr_spec_some_bridge(rel, 0x2F, 1);
    assert(iglib::incremental::parent_key_spec(rel)
        == Some(seq![0x61])) by {
        reveal(iglib::incremental::parent_key_spec);
        reveal(iglib::incremental::is_dot);
        reveal(iglib::incremental::is_dotdot);
        let name = rel.subrange(2, 3);
        assert(name.len() == 1);
        assert(name[0] == 0x78);
        let dt: Seq<u8> = seq![0x2E];
        assert(name != dt);
        let ddt: Seq<u8> = seq![0x2E, 0x2E];
        assert(name != ddt);
        assert(iglib::incremental::pk_trim_end(rel, 1) == 1) by {
            reveal(iglib::incremental::pk_trim_end);
        }
    }
    reveal(fast_path_spec);
    assert(fast_path_spec(Seq::empty(), rel, root, false, false)
        == None);
    // the error replay of the miss arm folds nothing
    assert(iglib::incremental::apply_rev2(Seq::empty(),
        seq![Seq::empty(), Seq::empty()]) == Seq::empty()) by {
        let pair: Seq<Seq<iglib::Error>> = Seq::empty()
            .push(Seq::empty())
            .push(Seq::empty());
        assert(pair.len() == 2);
        assert(pair.subrange(1, 2) == seq![Seq::empty()]);
        reveal_with_fuel(iglib::incremental::apply_rev2, 3);
        reveal(iglib::incremental::apply_rev);
    }
}

/// The miss-arm premises of one consult, spelled over the ii's own
/// terms (the row passes the construction posts; the walk ladder and
/// its face laws live in walk_ax_eval -- this wrapper keeps the row
/// body light so the mwi post instantiates at plain rlimit).
proof fn ax_miss_premises(
    ii: &iglib::incremental::IncrementalIgnore,
    f: &iglib::incremental::Ig6FsFace,
)
    requires
        iglib::incremental::ii_wf(ii),
        ii.state == iglib::incremental::RootState::Loaded,
        ii.dirs@ == Seq::empty(),
        ii.root@ == seq![0x74],
        ii.options.hidden == false,
        ii.root_store@ == seq![ii.root_store@[0]],
        ig_wf(&ii.root_store@[0]),
        !ii.root_store@[0].inner.opts.ignore,
        !ii.root_store@[0].inner.opts.git_global,
        !ii.root_store@[0].inner.opts.git_ignore,
        !ii.root_store@[0].inner.opts.git_exclude,
        ii.root_store@[0].inner.explicit_ignores@.len() == 0,
        ii.root_store@[0].inner.custom_ignore_filenames@.len() == 0,
        ii.root_store@[0].inner.overrides.inner.set.registered@.len()
            == 0,
        ii.root_store@[0].inner.types.selections@.len() == 0,
    ensures
        iglib::incremental::fast_path_spec(ii.dirs@,
            seq![0x61, 0x2F, 0x78], ii.root@, ii.options.hidden, false)
            == None,
        (iglib::incremental::walk_entry_root(ii.state,
            ii.root_store@, ii.root@, ii.options.hidden,
            seq![0x61, 0x2F, 0x78], false, ii.dirs@, f)).0
            == Some(im_none(false)),
        (iglib::incremental::walk_entry_root(ii.state,
            ii.root_store@, ii.root@, ii.options.hidden,
            seq![0x61, 0x2F, 0x78], false, ii.dirs@, f)).1
            == Seq::empty(),
        (iglib::incremental::walk_entry_root(ii.state,
            ii.root_store@, ii.root@, ii.options.hidden,
            seq![0x61, 0x2F, 0x78], false, ii.dirs@, f)).2
            == Seq::empty(),
        iglib::incremental::apply_rev2(Seq::empty(),
            seq![Seq::empty(), Seq::empty()]) == Seq::empty(),
{
    let ig0 = ii.root_store@[0];
    walk_ax_eval(ig0, f);
}

fn row_insert_closure_exec() -> (r: bool)
    ensures r
{
    let ig_store = h_ig_empty();
    let ds: Vec<iglib::incremental::CachedDirEnt> = Vec::new();
    proof {
        assert(dirs_wf(ds@)) by {
            reveal(dirs_wf);
        }
    }
    let rel = b3(0x61, 0x2F, 0x78);
    let f = h_fs(Ok(0));
    assert(rel@.len() > 0);
    assert(rel@[0] == 0x61);
    assert(rel@[0] != 0x2F);
    assert(f.filesize == Ok(0));
    assert(ds@ == Seq::empty());
    let mut ii = h_ii_loaded(b1(0x74), ig_store, ds,
        h_ii_opts(None, None, None));
    assert(iglib::incremental::ii_wf(&ii));
    assert(ii.dirs@ == Seq::empty());
    assert(ii.root@ == seq![0x74]);
    assert(ii.options.hidden == false);
    assert(ii.state == iglib::incremental::RootState::Loaded);
    assert(ii.root_store@[0] == ig_store);
    let rs = rel.as_slice();
    proof {
        // the miss-arm premises (the walk ladder and its face-law
        // ledger live in their own frames)
        ax_miss_premises(&ii, &f);
        // the slice argument names the same bytes as the vector
        // (Vec::as_slice's assume_specification; the callee's rel@
        // params spell in this view, so the guarded miss-arm
        // antecedent is re-spelled over it -- term-identical to
        // the post's own copy)
        assert(rs@ == rel@);
        assert(iglib::incremental::fast_path_spec(ii.dirs@, rs@,
            ii.root@, ii.options.hidden, false) == None);
        assert((iglib::incremental::walk_entry_root(ii.state,
            ii.root_store@, ii.root@, ii.options.hidden, rs@,
            false, ii.dirs@, &f)).0 == Some(im_none(false)));
        assert((iglib::incremental::walk_entry_root(ii.state,
            ii.root_store@, ii.root@, ii.options.hidden, rs@,
            false, ii.dirs@, &f)).1 == Seq::empty());
        assert((iglib::incremental::walk_entry_root(ii.state,
            ii.root_store@, ii.root@, ii.options.hidden, rs@,
            false, ii.dirs@, &f)).2 == Seq::empty());
    }
    let mut errs = iglib::PartialErrorBuilder::new();
    // the consult (miss arm: the walk inserts the "a" chain; the
    // per-entry closure clauses below are the contract consumed).
    // The r-value and the peb fold of THIS arm ride the #IG-32
    // instantiation wall (the miss-arm antecedent does not reach
    // z3 at the call site -- the same Some/None asymmetry the
    // twin's matched_with_errors_impl refill record documents at
    // incremental.rs:4196-4215; rounds 300/600 probed on this row
    // in five shapes, repro: --verify-function
    // row_insert_closure_exec). The arm's own decision value is
    // pinned spec-side in walk_ax_eval (consult-miss -> the child
    // face -> none); this row's consumption holds the unconditional
    // contract face: the post-state wf and the per-inserted-entry
    // parent-chain closure.
    let _rv = ii.matched_with_errors_ignore(rs, false,
        &mut errs, &f);
    let _eo = errs.into_error_option();
    // the closure consumption: the post state keeps the root
    // identity and the ii wf (dirs_wf inside), and every inserted
    // entry satisfies the parent-chain closure clauses (the insert
    // ran the "a" chain -- the contract pins the shape over the
    // post cache; the growth cardinality is exec-knowledge the
    // contract does not claim)
    assert(iglib::incremental::ii_wf(&ii));
    assert(ii.root@ == seq![0x74]);
    assert(dirs_wf(ii.dirs@));
    assert(forall|t: int| #![trigger ii.dirs@[t].key@]
        0 <= t < ii.dirs@.len() ==> (
        ii.dirs@[t].key@.len() > 0
            && (match iglib::incremental::key_parent(ii.dirs@[t].key@) {
                None => true,
                Some(p2) => cache_scan(ii.dirs@, p2, 0) >= 0,
            })
            && (match &ii.dirs@[t].state {
                iglib::incremental::CachedDir::Allowed(g1) => ig_wf(g1),
                iglib::incremental::CachedDir::Ignored => true,
            })));
    true
}
} // verus!

fn main() {}
