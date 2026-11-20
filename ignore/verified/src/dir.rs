//! ignore 0.4.34 (pin `178cc027`) -- Verus twin, `dir.rs` (the
//! per-directory `Ignore` stack), batch IG5.
//!
//! Upstream: github.com/BurntSushi/ripgrep @
//! 178cc027e283fd965cb72d0a7395b219eada170c (crates/ignore = 0.4.34).
//! The upstream module (crates/ignore/src/dir.rs, 1700 lines) carries
//! the precedence spine of the whole crate: `Ignore::matched` (the
//! overrides / ignore-files / types cascade) and `Ignore::matched_ignore`
//! (the six-pool fold custom > `.ignore` > `.gitignore` >
//! `.git/info/exclude` > global > explicit, over the parent-chain
//! walk with the absolute-parent path-rewrite block of dir.rs:625-693
//! -- the fresh 2026-07 fix-wave seam: issues 3320 / 3376 / 3419 and
//! PR 3420; the upstream "ham-fisted" comment at dir.rs:627-633 is
//! transcribed verbatim at the rewrite model), plus the builder and
//! the ignore-file discovery faces.
//!
//! Batch depth allocation (real exec bodies verified here):
//! - `Ignore::matched` / `matched_ignore` / `matched_dir_entry` /
//!   `has_any_ignore_rules` -- the full precedence spine against the
//!   value specs `dir_matched_spec` / `dir_mi_spec` / the dentry spec;
//! - `strip_if_is_prefix` / the join model / the rewrite composition;
//! - `collect_ignore_files` (the IgnoreFilesFound table over an
//!   abstract read_dir entry face);
//! - `resolve_git_commondir` parsing over abstract file-read faces;
//! - the `add_parents` quirk-fold (the has_git mask, the
//!   is_absolute_parent stamp, the has_absolute_parent_rules
//!   accumulation) over trusted per-parent construction faces;
//! - `IgnoreBuilder::new` + every setter + `build`/`build_with_cwd`
//!   (the global gitignore as a face parameter -- inventory section
//!   9: "env reads modeled as face parameters, not env reads").
//!
//! Trusted-contract legs (external_body, full contracts; body proofs
//! deferred per the #IG-16 lesson):
//! - `add_child_path_with_found` (the create_gitignore decision table;
//!   the four slot gates spell out upstream dir.rs:374-497 exactly);
//! - `create_gitignore` (the fs legs; abstract creation faces
//!   `created_matcher_face` / `created_errs_face`).
//!
//! Modeling declarations (the divergences that matter):
//! - **Chain as Vec:** upstream `IgnoreInner` is a persistent
//!   Arc-parent tree walked by the `Parents` iterator (self first,
//!   then ancestors, dir.rs:760-779); the twin stores the same walk
//!   order as `nodes: Vec<IgnoreNode>` (`nodes[0]` = self, last = the
//!   builder root) with the shape invariant `ig_shape`: a non-absolute
//!   prefix then an absolute-parent suffix to the builder root -- what
//!   the take_while / skip_while seam of dir.rs:593 / :658-660
//!   observes on well-formed stacks. The Arc sharing, the
//!   `compiled` RwLock+Weak matcher cache and the `Arc::ptr_eq`
//!   identity assertions sit outside the value model: a cache hit
//!   (dir.rs:231-240) returns a node that add_child_path would
//!   rebuild identically at the same directory with the same opts
//!   (matcher contents are a pure function of dir + found files +
//!   opts), recorded as the trusted face equation; the two multi-root
//!   cache tests stay runtime rows.
//! - **Per-node vs shared fields:** the upstream fields carried in
//!   Arc-shared clones of one builder value (overrides, types,
//!   explicit_ignores, custom_ignore_filenames, git_global_matcher,
//!   opts, global_gitignores_relative_to, compiled -- dir.rs:114-169)
//!   sit once in the twin's `IgnoreInner`; the per-node fields (dir,
//!   is_absolute_parent, has_absolute_parent_rules, has_git, the
//!   four directory matchers) sit on `IgnoreNode`.
//! - **Consuming builders/stacks:** upstream clones Arcs; the twin's
//!   `build`/`add_child`/`add_parents` take `self` by value (the
//!   sharing tier is not value-observable; owned data has no Clone
//!   face in this Verus build). `matched`/`matched_ignore` borrow.
//! - **Payloads owned:** `IgnoreMatch<'a>` borrows the matched glob
//!   (dir.rs:34-67); the twin payload `IgmPayload` carries owned
//!   copies (the crate convention since IG3), with `IgmOrigSpec`
//!   preserving the pool distinction (Override/Gitignore/Types/Hidden
//!   -- `IgnoreMatchInner`'s four variants) and the matched glob's
//!   five-field view.
//! - **fs faces:** canonicalize, existence/metadata probes and file
//!   reads are replaced by abstract input faces: `IgnoreFilesFound`
//!   is "what a read_dir / probe finds" (the found-set carries the
//!   same information the None arm fetches via stats -- the two arms
//!   agree whenever the fs does, per the upstream comment at
//!   dir.rs:702-708); the `git_type` probe face is
//!   `Option<bool>` (Some(ft.is_file())); the commondir reads ride
//!   the `ReadOutcome` face of `resolve_git_commondir`.
//! - **std Path::join** is `join_bytes` (runtime STDJOIN probe rows
//!   pin the model): a rooted rel replaces the base, else the base
//!   gets one `/` unless empty or already separator-terminated; an
//!   EMPTY rel still appends the separator (`join("/a","") == "/a/"`,
//!   host probe 2026-11-17).
//! - **`Path::new(".")` equality:** upstream
//!   `ig.inner.dir.as_path() == Path::new(".")` (dir.rs:645) is
//!   component equality; the twin compares bytes against `.` and
//!   `./` (the reachable walk-root spellings; the `././`-style
//!   Path-equal repeats cannot occur as walk dirs -- recorded, not
//!   modeled; the runtime S-probe pins the std family).

use vstd::prelude::*;
use vstd::seq::Seq;

use super::gitignore::{
    copy_glob, gi_decide, gi_is_empty_view, gi_strip_spec, Glob as GiGlob,
    Gitignore, globs_field_view, RegisteredGlob, root_strip_view,
};
use super::overrides::{
    Glob as OvGlob, GlobInner as OvGlobInner, ov_matched_spec, Override,
};
use super::pathutil::{is_hidden_path_only, is_hidden_path_only_spec};
use super::pathutil::{strip_prefix, strip_prefix_spec};
use super::types::types_wf;
use super::types::{
    copy_fdef, Glob as TyGlob, GlobInner as TyGlobInner, ty_matched_spec, Types,
};
use super::{
    error_with_path, is_io_spec, with_path_payload, Error, IoErrorFace,
    Match, PathBytes,
};

verus! {

// The Vec push-index axiom group (the #IG-12 recipe: one broadcast
// per module makes the push posts chain to seq indices).
broadcast use vstd::seq::group_seq_axioms;

// ===========================================================================
// exec byte-literal carriers (spec identity via push posts)
// ===========================================================================

/// The `"."` literal (the rewrite block's root special case).
pub fn dot_lit() -> (r: Vec<u8>)
    ensures r@ == seq![0x2E]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2E);
    v
}

/// The `"./"` literal (dir.rs:538, :648-651).
pub fn dot_slash_lit() -> (r: Vec<u8>)
    ensures r@ == seq![0x2E, 0x2F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2E);
    v.push(0x2F);
    v
}

/// The `"/"` literal (dir.rs:654).
pub fn slash_lit() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v
}

/// The `".ignore"` literal (dir.rs:351, :428).
pub fn ignore_lit() -> (r: Vec<u8>)
    ensures r@ == seq![0x2E, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2E);
    v.push(0x69);
    v.push(0x67);
    v.push(0x6E);
    v.push(0x6F);
    v.push(0x72);
    v.push(0x65);
    v
}

/// The `".gitignore"` literal (dir.rs:353, :441).
pub fn gitignore_lit() -> (r: Vec<u8>)
    ensures
        r@ == seq![0x2E, 0x67, 0x69, 0x74, 0x69, 0x67, 0x6E, 0x6F, 0x72,
            0x65]
{
    let mut v: Vec<u8> = Vec::new();
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

/// The `".git"` literal (dir.rs:355, :379, :1096).
pub fn dot_git_lit() -> (r: Vec<u8>)
    ensures r@ == seq![0x2E, 0x67, 0x69, 0x74]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2E);
    v.push(0x67);
    v.push(0x69);
    v.push(0x74);
    v
}

/// The `".jj"` literal (dir.rs:357, :385).
pub fn dot_jj_lit() -> (r: Vec<u8>)
    ensures r@ == seq![0x2E, 0x6A, 0x6A]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2E);
    v.push(0x6A);
    v.push(0x6A);
    v
}

/// The `"info/exclude"` literal (dir.rs:459).
pub fn info_exclude_lit() -> (r: Vec<u8>)
    ensures
        r@ == seq![
            0x69, 0x6E, 0x66, 0x6F, 0x2F, 0x65, 0x78, 0x63, 0x6C, 0x75,
            0x64, 0x65,
        ]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x69);
    v.push(0x6E);
    v.push(0x66);
    v.push(0x6F);
    v.push(0x2F);
    v.push(0x65);
    v.push(0x78);
    v.push(0x63);
    v.push(0x6C);
    v.push(0x75);
    v.push(0x64);
    v.push(0x65);
    v
}

/// The `"gitdir: "` literal (dir.rs:1114, :1117).
pub fn gitdir_lit() -> (r: Vec<u8>)
    ensures
        r@ == seq![0x67, 0x69, 0x74, 0x64, 0x69, 0x72, 0x3A, 0x20]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x67);
    v.push(0x69);
    v.push(0x74);
    v.push(0x64);
    v.push(0x69);
    v.push(0x72);
    v.push(0x3A);
    v.push(0x20);
    v
}

/// Byte-slice equality at the spec tier (`a@ == b@`). (Vec of u8
/// equality is decided positionally; the ensures pins it to the seq
/// view. Trusted-contract leg, the IG4 `bytes_eq_exec` precedent:
/// positional slice equality, runtime-pinned; deferred with the
/// seq-extensionality batch work.)
#[verifier::external_body]
pub fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures r == (a@ == b@)
{
    unimplemented!() // trusted face: per-position comparison
}

// ===========================================================================
// IgnoreOptions -- upstream dir.rs:69-90
// ===========================================================================

/// Origin struct (dir.rs:71-90); every field doc verbatim.
pub struct IgnoreOptions {
    /// Whether to ignore hidden file paths or not.
    pub hidden: bool,
    /// Whether to read .ignore files.
    pub ignore: bool,
    /// Whether to respect any ignore files in parent directories.
    pub parents: bool,
    /// Whether to read git's global gitignore file.
    pub git_global: bool,
    /// Whether to read .gitignore files.
    pub git_ignore: bool,
    /// Whether to read .git/info/exclude files.
    pub git_exclude: bool,
    /// Whether to ignore files case insensitively
    pub ignore_case_insensitive: bool,
    /// Whether a git repository must be present in order to apply any
    /// git-related ignore rules.
    pub require_git: bool,
}

// ===========================================================================
// the chain value model
// ===========================================================================

/// One directory's node of the matcher chain: the upstream per-`IgnoreInner`
/// fields (dir.rs:114-169: dir, is_absolute_parent,
/// has_absolute_parent_rules, has_git, the four directory matchers).
pub struct IgnoreNode {
    /// The directory this node was built from (upstream `dir: PathBuf`,
    /// dir.rs:124).
    pub dir: Vec<u8>,
    /// Whether this is an absolute parent matcher, as added by
    /// add_parent (upstream dir.rs:134-137).
    pub is_absolute_parent: bool,
    /// Whether any absolute parent has ignore rules. When none do,
    /// matching can skip rewriting the candidate path for those
    /// parents. (upstream dir.rs:136-138)
    pub has_absolute_parent_rules: bool,
    /// Whether this directory contains a .git sub-directory (upstream
    /// dir.rs:165-166; the require_git tier's any_git input; the .jj
    /// worktree arm sets it too).
    pub has_git: bool,
    /// The matcher for custom ignore files (upstream dir.rs:155-156).
    pub custom_ignore_matcher: Gitignore,
    /// The matcher for .ignore files (upstream dir.rs:157-158).
    pub ignore_matcher: Gitignore,
    /// The matcher for .gitignore files (upstream dir.rs:161-162).
    pub git_ignore_matcher: Gitignore,
    /// Special matcher for `.git/info/exclude` files (upstream
    /// dir.rs:163-164).
    pub git_exclude_matcher: Gitignore,
}

/// The Arc-shared builder context: the upstream `IgnoreInner` and
/// `IgnoreBuilder` fields that every node of one built stack clones
/// verbatim (dir.rs:114-169, :781-806). `global_gitignores_relative_to`
/// is a matching-inert record (build-time discovery only); the
/// `compiled` cache is the trusted face (see the header note).
pub struct IgnoreInner {
    /// The root directory path for this ignore matcher (upstream
    /// IgnoreBuilder.dir, dir.rs:784-785; only "" is ever set).
    pub dir: Vec<u8>,
    /// An override matcher (default is empty).
    pub overrides: Override,
    /// A file type matcher.
    pub types: Types,
    /// The directory that gitignores should be interpreted relative to.
    /// Usually this is the directory containing the gitignore file. But
    /// in some cases, like for global gitignores or for gitignores
    /// specified explicitly, this should generally be set to the current
    /// working directory. This is only used for global gitignores or
    /// "explicit" gitignores.
    ///
    /// When `None`, this means the CWD could not be determined or is
    /// unknown. In this case, global gitignore files are ignored because
    /// they otherwise cannot be matched correctly. (upstream
    /// dir.rs:139-150, verbatim)
    pub global_gitignores_relative_to: Option<Vec<u8>>,
    /// Explicit global ignore matchers specified by the caller (upstream
    /// dir.rs:151-152).
    pub explicit_ignores: Vec<Gitignore>,
    /// Ignore files used in addition to `.ignore` (upstream
    /// `custom_ignore_filenames: Arc<Vec<OsString>>`, dir.rs:153-154;
    /// byte carriers here).
    pub custom_ignore_filenames: Vec<Vec<u8>>,
    /// A global gitignore matcher, usually from $XDG_CONFIG_HOME/git/ignore
    /// (upstream dir.rs:158-159).
    pub git_global_matcher: Gitignore,
    /// Ignore config (upstream dir.rs:167-168).
    pub opts: IgnoreOptions,
}

/// Ignore is a matcher useful for recursively walking one or more
/// directories. (upstream doc dir.rs:92, verbatim)
///
/// The twin carries the persistent parent chain as the head-first node
/// vec (`nodes[0]` = this matcher, last = the builder root; the
/// `Parents` iteration order of dir.rs:760-779) plus the per-root
/// `absolute_base` (the 2026-07 fix-wave's root-scoping carrier:
/// PR 3420 moved it off the shared Arc onto the per-root wrapper,
/// upstream dir.rs:94-111 doc quoted there; kept verbatim as
/// `Option<Vec<u8>>`).
pub struct Ignore {
    /// The shared builder context (upstream: the Arc-shared fields).
    pub inner: IgnoreInner,
    /// nodes[0] = self ... nodes[len-1] = the builder root.
    pub nodes: Vec<IgnoreNode>,
    /// The canonicalized base of the root this matcher serves
    /// (upstream `absolute_base: Option<Arc<PathBuf>>`).
    pub absolute_base: Option<Vec<u8>>,
}

/// The chain shape: a (possibly empty) non-absolute prefix, then
/// absolute-parent nodes up to the builder root (what the
/// take_while / skip_while seam of dir.rs:593 / :658-660 observes on
/// well-formed stacks).
pub open spec fn ig_shape(nodes: Seq<IgnoreNode>) -> bool {
    nodes.len() >= 1
        && nodes[nodes.len() - 1].is_absolute_parent
        && forall|i: int| #![trigger nodes[i]]
            0 <= i < nodes.len() - 1 ==>
            (nodes[i].is_absolute_parent
                ==> nodes[i + 1].is_absolute_parent)
}

/// The full stack well-formedness (the chain shape plus the IG4
/// `Types::matched` leg's requirement -- the 19-leg-set convention:
/// the legs are consumed as trusted interfaces, not re-proved here).
pub open spec fn ig_wf(ig: &Ignore) -> bool {
    ig_shape(ig.nodes@) && types_wf(&ig.inner.types)
}

/// First-index scan helper: the first index >= i whose node is an
/// absolute parent (len when none).
pub open spec fn first_abs(nodes: Seq<IgnoreNode>, i: int) -> int
    decreases nodes.len() - i
{
    if i >= nodes.len() {
        nodes.len() as int as int
    } else if nodes[i].is_absolute_parent {
        i
    } else {
        first_abs(nodes, i + 1)
    }
}

/// The any-git fold over the whole chain (upstream
/// `self.parents().any(|ig| ig.inner.has_git)`, dir.rs:590-591).
pub open spec fn any_has_git(nodes: Seq<IgnoreNode>, i: int) -> bool
    decreases nodes.len() - i
{
    if i >= nodes.len() {
        false
    } else {
        nodes[i].has_git || any_has_git(nodes, i + 1)
    }
}

/// The require_git gate: with require_git off, git rules apply
/// everywhere (upstream dir.rs:590: `let any_git = !opts.require_git
/// || ...`).
pub open spec fn ig_any_git(ig: &Ignore) -> bool {
    !ig.inner.opts.require_git || any_has_git(ig.nodes@, 0)
}

// ===========================================================================
// IgmPayload -- upstream IgnoreMatch / IgnoreMatchInner (dir.rs:34-67)
// ===========================================================================

/// IgnoreMatch represents information about where a match came from
/// when using the `Ignore` matcher. (upstream doc dir.rs:34-35,
/// verbatim; the twin payload is owned -- the upstream lifetime is
/// elided per the crate convention.)
pub enum IgmOrigSpec {
    /// The override arm (upstream IgnoreMatchInner::Override,
    /// dir.rs:45; the matched glob's five-field view, None for
    /// Override's unmatched glob).
    Ov(Option<(Seq<u8>, Seq<u8>, bool, bool, Option<Seq<u8>>)>),
    /// The gitignore pool arm (upstream dir.rs:46; ANY of the six
    /// gitignore-backed pools custom/.ignore/.gitignore/exclude/
    /// global/explicit decorates this way).
    Gi((Seq<u8>, Seq<u8>, bool, bool, Option<Seq<u8>>)),
    /// The types arm (upstream dir.rs:47; the def name view).
    Ty(Option<Seq<u8>>),
    /// The hidden arm (upstream dir.rs:48).
    Hidden,
}

/// The exec-tier origin marker (the payload twin of
/// `IgnoreMatchInner`, dir.rs:44-49): the pool discriminator plus
/// the five-field glob view carried as exec byte vectors.
pub enum IgmOrig {
    /// The override arm (None = the override unmatched glob).
    Ov(Option<(Vec<u8>, Vec<u8>, bool, bool, Option<Vec<u8>>)>),
    /// The gitignore-pool arm (any of the six backed pools).
    Gi((Vec<u8>, Vec<u8>, bool, bool, Option<Vec<u8>>)),
    /// The types arm (the def name; None = the types unmatched glob).
    Ty(Option<Vec<u8>>),
    /// The hidden arm.
    Hidden,
}

/// The twin payload twin of `IgnoreMatch(IgnoreMatchInner)`.
pub struct IgmPayload {
    /// The gitignore-pool glob copy (the Gi arm's decoration).
    pub gi_glob: Option<GiGlob>,
    /// The override arm's glob copy.
    pub ov_glob: Option<OvGlob>,
    /// The types arm's glob copy.
    pub ty_glob: Option<TyGlob>,
    /// Which pool the verdict came from, with its view payload.
    pub orig: IgmOrig,
}

/// The spec view of one exec origin marker (byte views lifted).
pub open spec fn orig_view(o: &IgmOrig) -> IgmOrigSpec {
    match o {
        IgmOrig::Ov(inner) => match inner {
            Some(t) => IgmOrigSpec::Ov(Some((
                t.0@,
                t.1@,
                t.2,
                t.3,
                match t.4 {
                    Some(v) => Some(v@),
                    None => None,
                },
            ))),
            None => IgmOrigSpec::Ov(None),
        },
        IgmOrig::Gi(t) => IgmOrigSpec::Gi((
            t.0@,
            t.1@,
            t.2,
            t.3,
            match t.4 {
                Some(v) => Some(v@),
                None => None,
            },
        )),
        IgmOrig::Ty(n) => match n {
            Some(v) => IgmOrigSpec::Ty(Some(v@)),
            None => IgmOrigSpec::Ty(None),
        },
        IgmOrig::Hidden => IgmOrigSpec::Hidden,
    }
}

/// The view of one final Match: outer Some iff a pool hit, the bool
/// whitelist side, the pool marker with the glob field view.
pub open spec fn ig_m_view(m: &Match<IgmPayload>)
    -> Option<(bool, IgmOrigSpec)>
{
    match m {
        Match::None => None,
        Match::Ignore(p) => Some((false, orig_view(&p.orig))),
        Match::Whitelist(p) => Some((true, orig_view(&p.orig))),
    }
}

/// The gitignore-pool slot view: exactly what `Gitignore::matched`
/// returns per its IG3 ensures (gi_decide over the matcher's stores
/// after the root strip), decorated into the Gi arm.
pub open spec fn gi_slot_view(
    globs: Seq<GiGlob>,
    registered: Seq<RegisteredGlob>,
    root: Seq<u8>,
    path: Seq<u8>,
    is_dir: bool,
) -> Option<(bool, IgmOrigSpec)> {
    match gi_decide(globs, registered, gi_strip_spec(root, path), is_dir) {
        None => None,
        Some((wl, i)) => Some((wl, IgmOrigSpec::Gi(globs_field_view(globs[i])))),
    }
}

/// The Option slot view used by both tiers (verdict + payload).
pub open spec fn opt_slot_view(
    s: Option<(bool, IgmPayload)>,
) -> Option<(bool, IgmOrigSpec)> {
    match s {
        None => None,
        Some((b, p)) => Some((b, orig_view(&p.orig))),
    }
}

/// Exec: run one gitignore-pool matcher and decompose (upstream
/// `.matched(path, is_dir).map(IgnoreMatch::gitignore)`, dir.rs:596-600
/// etc; the map's value law spelled per arm).
fn gi_slot_exec(
    gi: &Gitignore,
    path: &[u8],
    is_dir: bool,
) -> (r: Option<(bool, IgmPayload)>)
    ensures opt_slot_view(r)
        == gi_slot_view(
            gi.globs@,
            gi.set.registered@,
            gi.root.bytes@,
            path@,
            is_dir,
        )
{
    let m = gi.matched(path, is_dir);
    match m {
        Match::None => None,
        Match::Whitelist(g) => {
            let fv = glob_fv_exec(&g);
            let cg = copy_glob(&g);
            Some((true, IgmPayload {
                gi_glob: Some(cg),
                ov_glob: None,
                ty_glob: None,
                orig: IgmOrig::Gi(fv),
            }))
        }
        Match::Ignore(g) => {
            let fv = glob_fv_exec(&g);
            let cg = copy_glob(&g);
            Some((false, IgmPayload {
                gi_glob: Some(cg),
                ov_glob: None,
                ty_glob: None,
                orig: IgmOrig::Gi(fv),
            }))
        }
    }
}

// ===========================================================================
// matched_ignore -- the scan state and the six-pool fold
// ===========================================================================


/// Exec copy of one glob's five-field view (the orig payload carrier;
/// the bytes via the accessor ensures).
fn glob_fv_exec(
    g: &GiGlob,
) -> (r: (Vec<u8>, Vec<u8>, bool, bool, Option<Vec<u8>>))
    ensures
        orig_view(&IgmOrig::Gi(r))
            == IgmOrigSpec::Gi(globs_field_view(*g))
{
    let orig_s = g.original();
    let act_s = g.actual();
    let fmatch = match &g.from {
        Some(p) => {
            Some(vstd::slice::slice_to_vec(p.bytes.as_slice()))
        }
        None => None,
    };
    let r = (
        vstd::slice::slice_to_vec(orig_s),
        vstd::slice::slice_to_vec(act_s),
        g.is_whitelist(),
        g.is_only_dir(),
        fmatch,
    );
    proof {
        assert(r.0@ == orig_s@);
        assert(r.1@ == act_s@);
        assert(match r.4 {
            Some(v) => Some(v@),
            None => None,
        } == super::gitignore::from_view(g.from));
    }
    r
}

/// The five tracked slots + the git barrier bit of the two
/// matched_ignore loops (upstream dir.rs:583-589, :592).
pub struct MiScanSt {
    /// The custom-ignore pool slot verdict.
    pub m_custom: Option<(bool, IgmOrigSpec)>,
    /// The .ignore pool slot verdict.
    pub m_ignore: Option<(bool, IgmOrigSpec)>,
    /// The .gitignore pool slot verdict.
    pub m_gi: Option<(bool, IgmOrigSpec)>,
    /// The .git/info/exclude pool slot verdict.
    pub m_gi_exclude: Option<(bool, IgmOrigSpec)>,
    /// Whether a directory containing .git has been passed (the
    /// saw_git barrier, upstream dir.rs:592, :623, :690; it blocks
    /// the git pools of further-up directories -- the stops_at_git_dir
    /// semantics, dir.rs:1395-1416).
    pub saw_git: bool,
}

/// The empty-slot initial state (upstream dir.rs:583-589).
pub open spec fn mi_st_none() -> MiScanSt {
    MiScanSt {
        m_custom: None,
        m_ignore: None,
        m_gi: None,
        m_gi_exclude: None,
        saw_git: false,
    }
}

/// One loop-body step over a node (upstream dir.rs:593-624 for the
/// take_while loop and :658-691 for the absolute-parent loop; the
/// bodies are textually identical except for the path operand, which
/// the caller supplies -- the relative path in the first scan,
/// the joined rewrite in the second).
pub open spec fn mi_step(node: IgnoreNode, st: MiScanSt, path: Seq<u8>,
    is_dir: bool, any_git: bool,
) -> MiScanSt {
    let m_custom = if (st.m_custom matches None) {
        gi_slot_view(
            node.custom_ignore_matcher.globs@,
            node.custom_ignore_matcher.set.registered@,
            node.custom_ignore_matcher.root.bytes@,
            path,
            is_dir,
        )
    } else {
        st.m_custom
    };
    let m_ignore = if (st.m_ignore matches None) {
        gi_slot_view(
            node.ignore_matcher.globs@,
            node.ignore_matcher.set.registered@,
            node.ignore_matcher.root.bytes@,
            path,
            is_dir,
        )
    } else {
        st.m_ignore
    };
    let m_gi = if (any_git && !st.saw_git && st.m_gi matches None) {
        gi_slot_view(
            node.git_ignore_matcher.globs@,
            node.git_ignore_matcher.set.registered@,
            node.git_ignore_matcher.root.bytes@,
            path,
            is_dir,
        )
    } else {
        st.m_gi
    };
    let m_gi_exclude = if (any_git && !st.saw_git && st.m_gi_exclude matches None)
    {
        gi_slot_view(
            node.git_exclude_matcher.globs@,
            node.git_exclude_matcher.set.registered@,
            node.git_exclude_matcher.root.bytes@,
            path,
            is_dir,
        )
    } else {
        st.m_gi_exclude
    };
    MiScanSt {
        m_custom,
        m_ignore,
        m_gi,
        m_gi_exclude,
        saw_git: st.saw_git || node.has_git,
    }
}

/// The scan fold over nodes[k..b) (first scan: k=0, b=first_abs;
/// second scan: k=first_abs, b=len).
pub open spec fn mi_scan(
    nodes: Seq<IgnoreNode>,
    k: int,
    b: int,
    st: MiScanSt,
    path: Seq<u8>,
    is_dir: bool,
    any_git: bool,
) -> MiScanSt
    decreases b - k
{
    if k >= b {
        st
    } else {
        mi_scan(
            nodes,
            k + 1,
            b,
            mi_step(nodes[k], st, path, is_dir, any_git),
            path,
            is_dir,
            any_git,
        )
    }
}

/// `strip_if_is_prefix` (upstream dir.rs:1138-1145): Strips `prefix`
/// from `path` if it's a prefix, otherwise returns `path` unchanged.
/// (the byte-prefix strip arm of pathutil, per DP33's unix face).
pub open spec fn strip_keep(prefix: Seq<u8>, path: Seq<u8>) -> Seq<u8> {
    match strip_prefix_spec(prefix, path) {
        Some(s) => s,
        None => path,
    }
}

/// The push-tier prefix fold: s pushed with rel[0..k) (the join body
/// helper; k counts from the low end so the exec loop's invariant
/// starts at the seed).
pub open spec fn append_prefix(s: Seq<u8>, rel: Seq<u8>, k: int) -> Seq<u8>
    decreases k
{
    if k <= 0 {
        s
    } else {
        append_prefix(s, rel, k - 1).push(rel[k - 1])
    }
}

/// The std Path::join byte model (dir.rs:634's
/// `abs_parent_path.join(...)` and dir.rs:1057's
/// `dir_for_ignorefile.join(name)`), pinned by the runtime STDJOIN
/// probe rows: a ROOTED rel replaces the base; the base gets one `/`
/// unless empty or separator-terminated; an EMPTY rel still appends
/// the separator (`join("/a", "") == "/a/"`, host probe 2026-11-17).
pub open spec fn join_bytes(base: Seq<u8>, rel: Seq<u8>) -> Seq<u8> {
    if rel.len() > 0 && rel[0] == 0x2F {
        rel
    } else if base.len() > 0 && base[base.len() - 1] != 0x2F {
        append_prefix(base.push(0x2F), rel, rel.len() as int)
    } else {
        append_prefix(base, rel, rel.len() as int)
    }
}

/// The absolute-parent path rewrite (upstream dir.rs:626-656; the
/// fix-wave seam, comments verbatim below at the exec twin):
/// - no relative node above the barrier (the
///   `take_while(...).last()` is None): the path is used as-is;
/// - the deepest relative node's dir is Path-equal "." (the consult
///   `rg .` special case, dir.rs:640-647): the path is used as-is, so
///   the strip below can never mangle a hidden name;
/// - else strip "./" off the dir, strip the dir off the path, strip
///   a leading "/", then join onto the absolute base.
pub open spec fn mi_rewrite(
    nodes: Seq<IgnoreNode>,
    path: Seq<u8>,
    abs_base: Seq<u8>,
) -> Seq<u8> {
    let b = first_abs(nodes, 0);
    let rel = if b == 0 {
        path
    } else {
        let dir = nodes[b - 1].dir@;
        if dir == seq![0x2E] || dir == seq![0x2E, 0x2F] {
            path
        } else {
            let wds = strip_keep(seq![0x2E, 0x2F], dir);
            let rel_base = strip_keep(wds, path);
            strip_keep(seq![0x2F], rel_base)
        }
    };
    join_bytes(abs_base, rel)
}

/// The explicit-pool scan: `.rev()` consults the LATEST-added matcher
/// first (upstream dir.rs:694-699; DP25: later-added explicit
/// matchers win).
pub open spec fn mi_explicit(
    expls: Seq<Gitignore>,
    j: int,
    path: Seq<u8>,
    is_dir: bool,
) -> Option<(bool, IgmOrigSpec)>
    decreases j + 1
{
    if j < 0 {
        None
    } else {
        match gi_slot_view(
            expls[j].globs@,
            expls[j].set.registered@,
            expls[j].root.bytes@,
            path,
            is_dir,
        ) {
            None => mi_explicit(expls, j - 1, path, is_dir),
            Some(v) => Some(v),
        }
    }
}

/// The or-tier first-hit combinator (the `.or` cascade of
/// dir.rs:709-714: the first non-None slot wins).
pub open spec fn or_hit(
    a: Option<(bool, IgmOrigSpec)>,
    b: Option<(bool, IgmOrigSpec)>,
) -> Option<(bool, IgmOrigSpec)> {
    match a {
        None => b,
        Some(_) => a,
    }
}

/// The full `matched_ignore` value spec (upstream dir.rs:576-715):
/// the first scan over the relative prefix (nodes[0..first_abs)),
/// the after-barrier absolute-parent scan (nodes[first_abs..len)) under
/// `opts.parents && nodes[0].has_absolute_parent_rules &&
/// absolute_base.is_some()` -- with the REWRITTEN path, the explicit
/// `.rev()` pool and the global matcher (gated by any_git) on the
/// ORIGINAL path -- folded by the or-cascade
/// custom > .ignore > .gitignore > .git/info/exclude > global >
/// explicit. (NB the explicit and global pools never see the rewrite
/// -- the upstream shadowing: the `let path = abs_parent_path.join..`
/// binding closes at the block end, dir.rs:693, so dir.rs:694-707
/// read the outer path. Transcribed exactly.)
pub open spec fn dir_mi_spec(ig: &Ignore, path: Seq<u8>, is_dir: bool)
    -> Option<(bool, IgmOrigSpec)>
{
    let any_git = ig_any_git(ig);
    let b = first_abs(ig.nodes@, 0);
    let st1 = mi_scan(ig.nodes@, 0, b, mi_st_none(), path, is_dir, any_git);
    let st2 = match ig.absolute_base {
        Some(abs_base_val) => if ig.inner.opts.parents
            && ig.nodes@[0].has_absolute_parent_rules
        {
            let path2 = mi_rewrite(ig.nodes@, path, abs_base_val@);
            mi_scan(ig.nodes@, b, (ig.nodes@.len() as int), st1, path2, is_dir, any_git)
        } else {
            st1
        },
        None => st1,
    };
    let m_global = if any_git {
        gi_slot_view(
            ig.inner.git_global_matcher.globs@,
            ig.inner.git_global_matcher.set.registered@,
            ig.inner.git_global_matcher.root.bytes@,
            path,
            is_dir,
        )
    } else {
        None
    };
    let m_explicit = mi_explicit(
        ig.inner.explicit_ignores@,
        (ig.inner.explicit_ignores@.len() - 1) as int,
        path,
        is_dir,
    );
    or_hit(
        st2.m_custom,
        or_hit(
            st2.m_ignore,
            or_hit(
                st2.m_gi,
                or_hit(st2.m_gi_exclude, or_hit(m_global, m_explicit)),
            ),
        ),
    )
}

// ===========================================================================
// has_any_ignore_rules -- upstream dir.rs:499-512
// ===========================================================================

/// Upstream doc (dir.rs:499, verbatim):
///   "Returns true if at least one type of ignore rule should be
///    matched."
pub open spec fn ig_has_any_rules_spec(ig: &Ignore) -> bool {
    let opts = ig.inner.opts;
    opts.ignore
        || opts.git_global
        || opts.git_ignore
        || opts.git_exclude
        || ig.inner.custom_ignore_filenames@.len() > 0
        || ig.inner.explicit_ignores@.len() > 0
}

/// The exec twin (dir.rs:500-512, verbatim flow).
pub fn ig_has_any_rules(ig: &Ignore) -> (r: bool)
    ensures r == ig_has_any_rules_spec(ig)
{
    let o = &ig.inner.opts;
    if o.ignore || o.git_global || o.git_ignore || o.git_exclude {
        return true;
    }
    ig.inner.custom_ignore_filenames.len() > 0
        || ig.inner.explicit_ignores.len() > 0
}

// ===========================================================================
// the exec scan mirrors
// ===========================================================================

/// The exec slot state (the payload-carrying twin of MiScanSt).
pub struct MiSlots {
    /// The custom pool slot.
    pub m_custom: Option<(bool, IgmPayload)>,
    /// The .ignore pool slot.
    pub m_ignore: Option<(bool, IgmPayload)>,
    /// The .gitignore pool slot.
    pub m_gi: Option<(bool, IgmPayload)>,
    /// The .git/info/exclude pool slot.
    pub m_gi_exclude: Option<(bool, IgmPayload)>,
    /// The git barrier bit.
    pub saw_git: bool,
}

/// The view bridge MiSlots -> MiScanSt.
pub open spec fn slots_spec(st: &MiSlots) -> MiScanSt {
    MiScanSt {
        m_custom: opt_slot_view(st.m_custom),
        m_ignore: opt_slot_view(st.m_ignore),
        m_gi: opt_slot_view(st.m_gi),
        m_gi_exclude: opt_slot_view(st.m_gi_exclude),
        saw_git: st.saw_git,
    }
}

/// The prefix-side any-fold over nodes[0..i).
pub open spec fn any_has_git_prefix(nodes: Seq<IgnoreNode>, i: int) -> bool
    decreases i
{
    if i <= 0 {
        false
    } else {
        any_has_git_prefix(nodes, i - 1) || nodes[i - 1].has_git
    }
}

/// The prefix/suffix bridge: folding [0..len) any-has-git equals the
/// suffix fold from 0 (induction on the suffix start).
proof fn any_has_git_prefix_bridge(
    nodes: Seq<IgnoreNode>,
    i: int,
)
    requires 0 <= i <= nodes.len()
    ensures any_has_git_prefix(nodes, nodes.len() as int)
        == (any_has_git_prefix(nodes, i) || any_has_git(nodes, i))
    decreases nodes.len() - i
{
    if i == nodes.len() {
        assert(any_has_git(nodes, i) == false);
    } else {
        any_has_git_prefix_bridge(nodes, i + 1);
        assert(any_has_git_prefix(nodes, nodes.len() as int)
            == (any_has_git_prefix(nodes, i) || any_has_git(nodes, i)));
    }
}

/// The one-step unfolding of the prefix fold (the loop bridge).
proof fn any_has_git_prefix_step(nodes: Seq<IgnoreNode>, i: int)
    requires 0 <= i < nodes.len()
    ensures any_has_git_prefix(nodes, i + 1)
        == (any_has_git_prefix(nodes, i) || nodes[i].has_git)
{
}

/// The range lemma for the first_abs scan.
proof fn first_abs_bounds(nodes: Seq<IgnoreNode>, i: int)
    requires 0 <= i <= nodes.len()
    ensures 0 <= first_abs(nodes, i) <= nodes.len()
    decreases nodes.len() - i
{
    if i < nodes.len() {
        first_abs_bounds(nodes, i + 1);
    }
}

/// The prefix-skip lemma: a non-abs prefix does not move the
/// barrier scan.
proof fn first_abs_none_prefix(nodes: Seq<IgnoreNode>, k: int, i: int)
    requires k <= i <= nodes.len()
    ensures (forall|q: int| k <= q < i ==>
                !nodes[q].is_absolute_parent)
        ==> first_abs(nodes, k) == first_abs(nodes, i)
    decreases i - k
{
    if k < i {
        first_abs_none_prefix(nodes, k + 1, i);
    }
}

/// The first_abs exec carrier (the slice form; standalone so the
/// rewrite twin and the matcher both drive it; the bounds ride along
/// for the mi_scan_exec preconditions).
fn first_abs_exec(nodes: &[IgnoreNode]) -> (r: usize)
    ensures
        r as int == first_abs(nodes@, 0),
        0 <= r <= nodes.len(),
{
    let mut i: usize = 0;
    while i < nodes.len()
        invariant
            0 <= i <= nodes.len(),
            forall|q: int| 0 as int <= q < i ==>
                !nodes@[q].is_absolute_parent,
            first_abs(nodes@, 0) == first_abs(nodes@, i as int),
        decreases nodes.len() - i
    {
        if nodes[i].is_absolute_parent {
            proof {
                first_abs_bounds(nodes@, 0);
                assert(first_abs(nodes@, i as int) as int == i);
            }
            return i;
        }
        proof {
            first_abs_none_prefix(nodes@, i as int, i as int + 1);
        }
        i += 1;
    }
    proof {
        first_abs_bounds(nodes@, 0);
        assert(first_abs(nodes@, nodes.len() as int) == nodes.len() as int);
    }
    nodes.len()
}

/// The any_has_git exec carrier (the prefix fold, bridged at the end).
fn any_has_git_exec(nodes: &[IgnoreNode]) -> (r: bool)
    ensures r == any_has_git(nodes@, 0)
{
    let mut i: usize = 0;
    let mut acc = false;
    while i < nodes.len()
        invariant
            0 <= i <= nodes.len(),
            acc == any_has_git_prefix(nodes@, i as int),
        decreases nodes.len() - i
    {
        proof {
            any_has_git_prefix_step(nodes@, i as int);
        }
        acc = acc || nodes[i].has_git;
        i += 1;
    }
    proof {
        any_has_git_prefix_bridge(nodes@, 0);
    }
    acc
}

/// The scan fold's exec mirror (recursive; one node per level, the
/// same slot-update order as the loop body of upstream dir.rs:593-624
/// / :658-691).
fn mi_scan_exec(
    nodes: &[IgnoreNode],
    k: usize,
    b: usize,
    path: &[u8],
    is_dir: bool,
    any_git: bool,
    st: MiSlots,
) -> (r: MiSlots)
    requires k <= b, b <= nodes.len()
    ensures slots_spec(&r)
        == mi_scan(nodes@, k as int, b as int, slots_spec(&st), path@,
            is_dir, any_git)
    decreases b - k
{
    if k >= b {
        return st;
    }
    let mut m_custom = st.m_custom;
    let mut m_ignore = st.m_ignore;
    let mut m_gi = st.m_gi;
    let mut m_gi_exclude = st.m_gi_exclude;
    let saw_git_old = st.saw_git;
    if m_custom.is_none() {
        m_custom = gi_slot_exec(&nodes[k].custom_ignore_matcher, path, is_dir);
    }
    if m_ignore.is_none() {
        m_ignore = gi_slot_exec(&nodes[k].ignore_matcher, path, is_dir);
    }
    if any_git && !saw_git_old && m_gi.is_none() {
        m_gi = gi_slot_exec(&nodes[k].git_ignore_matcher, path, is_dir);
    }
    if any_git && !saw_git_old && m_gi_exclude.is_none() {
        m_gi_exclude =
            gi_slot_exec(&nodes[k].git_exclude_matcher, path, is_dir);
    }
    let st2 = MiSlots {
        m_custom,
        m_ignore,
        m_gi,
        m_gi_exclude,
        saw_git: saw_git_old || nodes[k].has_git,
    };
    proof {
        reveal(mi_step);
        reveal(mi_scan);
    }
    mi_scan_exec(nodes, k + 1, b, path, is_dir, any_git, st2)
}

/// `strip_if_is_prefix` (upstream dir.rs:1138-1145) -- Upstream doc:
///   "Strips `prefix` from `path` if it's a prefix, otherwise
///    returns the given `path` unchanged."
fn strip_if_prefix_exec<'p, 'a>(
    prefix: &'p [u8],
    path: &'a [u8],
) -> (r: &'a [u8])
    ensures r@ == strip_keep(prefix@, path@)
{
    match strip_prefix(prefix, path) {
        Some(p) => p,
        None => path,
    }
}

/// The std Path::join exec carrier (the join_bytes model).
fn join_exec(base: &[u8], rel: &[u8]) -> (r: Vec<u8>)
    ensures r@ == join_bytes(base@, rel@)
{
    if rel.len() > 0 && rel[0] == 0x2F {
        return vstd::slice::slice_to_vec(rel);
    }
    let need_sep: bool =
        base.len() > 0 && base[base.len() - 1] != 0x2F;
    let mut r: Vec<u8> = vstd::slice::slice_to_vec(base);
    if need_sep {
        r.push(0x2F);
    }
    let mut k: usize = 0;
    while k < rel.len()
        invariant
            0 <= k <= rel.len(),
            r@ == append_prefix(
                (if need_sep { base@.push(0x2F) } else { base@ }),
                rel@,
                k as int,
            ),
        decreases rel.len() - k
    {
        proof {
            reveal(append_prefix);
        }
        r.push(rel[k]);
        k += 1;
    }
    proof {
        reveal(join_bytes);
        reveal(append_prefix);
    }
    r
}

/// The absolute-parent rewrite's exec twin (upstream dir.rs:626-656;
/// the fix-wave seam. The upstream comments, verbatim:
///   "What we want to do here is take the absolute base path of
///    this directory and join it with the path we're searching.
///    The main issue we want to avoid is accidentally duplicating
///    directory components, so we try to strip any common prefix
///    off of `path`. Overall, this seems a little ham-fisted, but
///    it does fix a nasty bug. It should do fine until we overhaul
///    this crate.")
/// and the special case (dir.rs:639-647):
///   "This is a weird special case when ripgrep users search with
///    just a `.`, as some tools do automatically (like consult).
///    In this case, if we don't bail out now, the code below will
///    strip a leading `.` from `path`, which might mangle a hidden
///    file name!"
fn mi_rewrite_exec(
    nodes: &[IgnoreNode],
    path: &[u8],
    base: &[u8],
) -> (r: Vec<u8>)
    ensures r@ == mi_rewrite(nodes@, path@, base@)
{
    let b = first_abs_exec(nodes);
    if b == 0 {
        return join_exec(base, path);
    }
    let dir = nodes[b - 1].dir.as_slice();
    let dot = dot_lit();
    let ds = dot_slash_lit();
    let sl = slash_lit();
    if bytes_eq(dir, dot.as_slice()) || bytes_eq(dir, ds.as_slice()) {
        return join_exec(base, path);
    }
    let without_dot_slash = strip_if_prefix_exec(ds.as_slice(), dir);
    let relative_base =
        strip_if_prefix_exec(without_dot_slash, path);
    let no_lead = strip_if_prefix_exec(sl.as_slice(), relative_base);
    join_exec(base, no_lead)
}

/// The explicit-pool scan's exec mirror (rev: newest first).
fn mi_explicit_exec(
    expls: &[Gitignore],
    j: usize,
    path: &[u8],
    is_dir: bool,
) -> (r: Option<(bool, IgmPayload)>)
    requires j <= expls.len()
    ensures opt_slot_view(r)
        == mi_explicit(expls@, (j as int) - 1, path@, is_dir)
    decreases j
{
    if j == 0 {
        return None;
    }
    let v = gi_slot_exec(&expls[j - 1], path, is_dir);
    match v {
        Some(_) => v,
        None => mi_explicit_exec(expls, j - 1, path, is_dir),
    }
}

/// The or-tier exec combinator (Match::or's Option-side mirror).
fn or_slot_exec(
    a: Option<(bool, IgmPayload)>,
    b: Option<(bool, IgmPayload)>,
) -> (r: Option<(bool, IgmPayload)>)
    ensures opt_slot_view(r) == or_hit(opt_slot_view(a), opt_slot_view(b))
{
    match a {
        Some(_) => a,
        None => b,
    }
}

// ===========================================================================
// Ignore::matched / matched_ignore / matched_dir_entry
// ===========================================================================

/// The precedence-spine methods.
impl Ignore {
    /// Performs matching only on the ignore files for this directory
    /// and all parent directories. (upstream doc dir.rs:576-577,
    /// verbatim)
    pub fn matched_ignore(&self, path: &[u8], is_dir: bool)
        -> (r: Match<IgmPayload>)
        requires ig_wf(self)
        ensures ig_m_view(&r) == dir_mi_spec(self, path@, is_dir)
    {
        let any_git = !self.inner.opts.require_git
            || any_has_git_exec(self.nodes.as_slice());
        let b = first_abs_exec(self.nodes.as_slice());

        // First scan: the relative prefix (upstream dir.rs:593's
        // take_while arm).
        let st1 = mi_scan_exec(
            self.nodes.as_slice(),
            0,
            b,
            path,
            is_dir,
            any_git,
            MiSlots {
                m_custom: None,
                m_ignore: None,
                m_gi: None,
                m_gi_exclude: None,
                saw_git: false,
            },
        );

        // Second scan: the absolute-parent zone (upstream dir.rs:625-693).
        let mut st = st1;
        if self.inner.opts.parents
            && self.nodes[0].has_absolute_parent_rules
            && self.absolute_base.is_some()
        {
            let base_copy: Vec<u8> = match &self.absolute_base {
                Some(v) => vstd::slice::slice_to_vec(v.as_slice()),
                None => Vec::new(),
            };
            let path2 = mi_rewrite_exec(
                self.nodes.as_slice(),
                path,
                base_copy.as_slice(),
            );
            st = mi_scan_exec(
                self.nodes.as_slice(),
                b,
                self.nodes.len(),
                path2.as_slice(),
                is_dir,
                any_git,
                st,
            );
        } else {
            proof {
                // the spec's after-barrier gate is closed -- st1 == st2
                assert(!self.inner.opts.parents
                    || !self.nodes@[0].has_absolute_parent_rules
                    || self.absolute_base@ matches None);
            }
        }

        // The explicit pool, newest first (dir.rs:694-699).
        let m_explicit = mi_explicit_exec(
            self.inner.explicit_ignores.as_slice(),
            self.inner.explicit_ignores.len(),
            path,
            is_dir,
        );

        // The global matcher, gated by any_git (dir.rs:700-707).
        let m_global = if any_git {
            gi_slot_exec(&self.inner.git_global_matcher, path, is_dir)
        } else {
            None
        };

        // The or-cascade (dir.rs:709-714).
        let c1 = or_slot_exec(st.m_custom, st.m_ignore);
        let c2 = or_slot_exec(c1, st.m_gi);
        let c3 = or_slot_exec(c2, st.m_gi_exclude);
        let c4 = or_slot_exec(c3, m_global);
        let c5 = or_slot_exec(c4, m_explicit);
        match c5 {
            None => Match::None,
            Some((true, p)) => Match::Whitelist(p),
            Some((false, p)) => Match::Ignore(p),
        }
    }

    /// Returns a match indicating whether the given file path should
    /// be ignored or not. (upstream doc dir.rs:526-529, verbatim:
    /// "The match contains information about its origin.")
    pub fn matched(&self, path: &[u8], is_dir: bool) -> (r: Match<IgmPayload>)
        requires ig_wf(self)
        ensures ig_m_view(&r) == dir_matched_spec(self, path@, is_dir)
    {
        // We need to be careful with our path. If it has a leading ./,
        // then strip it because it causes nothing but trouble.
        // (upstream dir.rs:535-537, verbatim)
        let ds = dot_slash_lit();
        let p: &[u8] = match strip_prefix(ds.as_slice(), path) {
            Some(s) => s,
            None => path,
        };

        // Match against the override patterns. If an override matches
        // regardless of whether it's whitelist/ignore, then we quit and
        // return that result immediately. Overrides have the highest
        // precedence. (upstream dir.rs:541-544, verbatim)
        if !self.inner.overrides.is_empty() {
            let mat = self.inner.overrides.matched(p, is_dir);
            match mat {
                Match::None => {}
                Match::Whitelist(g) => {
                    return Match::Whitelist(ov_payload_exec(&g, true));
                }
                Match::Ignore(g) => {
                    return Match::Ignore(ov_payload_exec(&g, false));
                }
            }
        }

        let mut whitelisted = Match::None;
        if ig_has_any_rules(self) {
            let mat = self.matched_ignore(p, is_dir);
            if mat.is_ignore() {
                return mat;
            } else if mat.is_whitelist() {
                whitelisted = mat;
            }
        }
        // (`self.inner.types.is_empty()` upstream, dir.rs:564)
        if self.inner.types.selections.len() == 0 {
            return whitelisted;
        }
        let mat = self.inner.types.matched(p, is_dir);
        match mat {
            Match::None => whitelisted,
            Match::Whitelist(g) => {
                Match::Whitelist(ty_payload_exec(&g, true))
            }
            Match::Ignore(g) => Match::Ignore(ty_payload_exec(&g, false)),
        }
    }

    /// Like `matched`, but works with a directory entry instead.
    /// (upstream doc dir.rs:514, verbatim; the DirEntry face here is
    /// the two-field {path, is_dir} projection -- on unix
    /// is_hidden_entry(dent) is pathutil::is_hidden_path_only over
    /// dent.path(), pathutil.rs:56-60.)
    pub fn matched_dir_entry(
        &self,
        dent_path: &[u8],
        dent_is_dir: bool,
    ) -> (r: Match<IgmPayload>)
        requires ig_wf(self)
        ensures
            ig_m_view(&r)
                == dir_matched_dentry_spec(self, dent_path@, dent_is_dir)
    {
        let m = self.matched(dent_path, dent_is_dir);
        if m.is_none() && self.inner.opts.hidden
            && is_hidden_path_only(dent_path)
        {
            return Match::Ignore(IgmPayload {
                gi_glob: None,
                ov_glob: None,
                ty_glob: None,
                orig: IgmOrig::Hidden,
            });
        }
        m
    }
}

// ===========================================================================
// the payload wraps (the map value laws)
// ===========================================================================

/// The wrap of one override glob payload (the value law of
/// `.map(IgnoreMatch::overrides)`, dir.rs:550; the override tier's
/// own verdict rides the Whitelist / Ignore arm).
fn ov_payload_exec(g: &OvGlob, wl: bool) -> (r: IgmPayload)
    ensures
        r.ov_glob@ matches Some(_),
        orig_view(&r.orig) == match g {
            OvGlob(OvGlobInner::UnmatchedIgnore) => IgmOrigSpec::Ov(None),
            OvGlob(OvGlobInner::Matched(gg)) => IgmOrigSpec::Ov(Some(
                globs_field_view(*gg),
            )),
        }
{
    match g {
        OvGlob(OvGlobInner::UnmatchedIgnore) => IgmPayload {
            gi_glob: None,
            ov_glob: Some(OvGlob(OvGlobInner::UnmatchedIgnore)),
            ty_glob: None,
            orig: IgmOrig::Ov(None),
        },
        OvGlob(OvGlobInner::Matched(gg)) => {
            let fv = glob_fv_exec(gg);
            let cg = copy_glob(gg);
            IgmPayload {
                gi_glob: None,
                ov_glob: Some(OvGlob(OvGlobInner::Matched(cg))),
                ty_glob: None,
                orig: IgmOrig::Ov(Some(fv)),
            }
        }
    }
}

/// The wrap of one types glob payload (`.map(IgnoreMatch::types)`,
/// dir.rs:566; the def name rides the Ty arm).
fn ty_payload_exec(g: &TyGlob, wl: bool) -> (r: IgmPayload)
    ensures
        r.ty_glob@ matches Some(_),
        orig_view(&r.orig) == match g {
            TyGlob { inner: TyGlobInner::UnmatchedIgnore } => IgmOrigSpec::Ty(None),
            TyGlob { inner: TyGlobInner::MatchedDef { def } } => {
                IgmOrigSpec::Ty(Some(def.name@))
            }
        }
{
    match g {
        TyGlob { inner: TyGlobInner::UnmatchedIgnore } => IgmPayload {
            gi_glob: None,
            ov_glob: None,
            ty_glob: Some(TyGlob { inner: TyGlobInner::UnmatchedIgnore }),
            orig: IgmOrig::Ty(None),
        },
        TyGlob { inner: TyGlobInner::MatchedDef { def } } => IgmPayload {
            gi_glob: None,
            ov_glob: None,
            ty_glob: Some(TyGlob {
                inner: TyGlobInner::MatchedDef { def: copy_fdef(def) },
            }),
            orig: IgmOrig::Ty(Some(
                vstd::slice::slice_to_vec(def.name.as_slice()),
            )),
        },
    }
}

// ===========================================================================
// the top-level spec (matched's spec, upstream dir.rs:530-574)
// ===========================================================================

/// The override slot's spec view: `Override::matched`'s IG4 ensures
/// decorated into the Ov arm.
pub open spec fn ov_slot_view(
    ov: &Override,
    path: Seq<u8>,
    is_dir: bool,
) -> Option<(bool, IgmOrigSpec)> {
    match ov_matched_spec(ov, path, is_dir) {
        None => None,
        Some((wl, inner)) => Some((wl, IgmOrigSpec::Ov(inner))),
    }
}

/// The types slot's spec view.
pub open spec fn ty_slot_view(
    t: &Types,
    path: Seq<u8>,
    is_dir: bool,
) -> Option<(bool, IgmOrigSpec)> {
    match ty_matched_spec(t, path, is_dir) {
        None => None,
        Some((wl, name)) => Some((wl, IgmOrigSpec::Ty(name))),
    }
}

/// The spec of `Ignore::matched` (upstream dir.rs:530-574): the
/// leading "./" strip, the overrides short-circuit (any non-None
/// override verdict wins outright), the matched_ignore call behind
/// has_any_ignore_rules with the ignore-early-return and the
/// whitelist carry, the types tier, the whitelisted fallthrough.
pub open spec fn dir_matched_spec(
    ig: &Ignore,
    path: Seq<u8>,
    is_dir: bool,
) -> Option<(bool, IgmOrigSpec)> {
    let p0 = strip_keep(seq![0x2E, 0x2F], path);
    // upstream dir.rs:545 `if !self.inner.overrides.is_empty()`
    let ov = if ig.inner.overrides.inner.set.registered@.len() > 0 {
        ov_slot_view(&ig.inner.overrides, p0, is_dir)
    } else {
        None
    };
    match ov {
        Some(_) => ov,
        None => {
            let mi = if ig_has_any_rules_spec(ig) {
                dir_mi_spec(ig, p0, is_dir)
            } else {
                None
            };
            match mi {
                Some((false, _)) => mi,
                _ => {
                    let wl_mi = match mi {
                        Some((true, _)) => mi,
                        _ => None,
                    };
                    // upstream dir.rs:564 `if !self.inner.types.is_empty()`
                    let ty = if ig.inner.types.selections@.len() > 0 {
                        ty_slot_view(&ig.inner.types, p0, is_dir)
                    } else {
                        None
                    };
                    match ty {
                        Some((false, _)) => ty,
                        _ => match ty {
                            Some((true, _)) => ty,
                            _ => wl_mi,
                        },
                    }
                }
            }
        }
    }
}

/// The spec of `matched_dir_entry` (upstream dir.rs:515-524): the
/// hidden tier fills a None verdict when the dentry path is hidden.
pub open spec fn dir_matched_dentry_spec(
    ig: &Ignore,
    path: Seq<u8>,
    is_dir: bool,
) -> Option<(bool, IgmOrigSpec)> {
    match dir_matched_spec(ig, path, is_dir) {
        Some(_) => dir_matched_spec(ig, path, is_dir),
        None => if ig.inner.opts.hidden && is_hidden_path_only_spec(path) {
            Some((false, IgmOrigSpec::Hidden))
        } else {
            None
        },
    }
}
// ===========================================================================
// IgnoreFilesFound + collect_ignore_files -- upstream dir.rs:337-367
// ===========================================================================

/// State for tracking what kinds of files ripgrep is interested in for
/// a given directory. (upstream struct dir.rs:736-743; doc
/// dir.rs:729-735, verbatim:
///   "This is computed over the entire set of files in a directory
///    instead of trying to stat each file individually. If a file is
///    present, it's only then that we stat it for more information,
///    instead of relying on the stat to determine its existence.")
pub struct IgnoreFilesFound {
    /// A `.ignore` file was found.
    pub has_ignore: bool,
    /// A `.gitignore` file was found.
    pub has_git_ignore: bool,
    /// A `.git` directory (or gitfile) was found.
    pub has_git_dir: bool,
    /// A `.jj` directory was found.
    pub has_jj_dir: bool,
    /// Per custom ignore filename, whether that file was found
    /// (upstream `custom_ignore_files: Vec<bool>`, dir.rs:742).
    pub custom_ignore_files: Vec<bool>,
}

/// The abstract read_dir entry face (upstream `fs::DirEntry`; only
/// `file_name` is consumed by collect_ignore_files, dir.rs:350).
pub struct FsDirEntryFace {
    /// The entry's file name.
    pub file_name: Vec<u8>,
}

/// Whether any of entries[0..i) carries the given file name (the
/// entry-scan fold backing every found bit).
pub open spec fn any_named(
    entries: Seq<FsDirEntryFace>,
    name: Seq<u8>,
    i: int,
) -> bool
    decreases i
{
    if i <= 0 {
        false
    } else {
        any_named(entries, name, i - 1) || entries[i - 1].file_name@ == name
    }
}

/// The suffix-fold: whether any entry in [i, len) carries the name
/// (the recursion carrier; the prefix form `any_named` is the public
/// view, connected by the psx bridge below).
pub open spec fn any_named_sfx(
    entries: Seq<FsDirEntryFace>,
    name: Seq<u8>,
    i: int,
) -> bool
    decreases entries.len() - i
{
    if i >= entries.len() {
        false
    } else {
        entries[i].file_name@ == name
            || any_named_sfx(entries, name, i + 1)
    }
}

/// The prefix/suffix bridge: both folds cover the same entries.
proof fn any_named_psx(
    entries: Seq<FsDirEntryFace>,
    name: Seq<u8>,
    j: int,
)
    requires 0 <= j <= entries.len()
    ensures any_named(entries, name, entries.len() as int)
        == (any_named(entries, name, j)
            || any_named_sfx(entries, name, j))
    decreases entries.len() - j
{
    if j < entries.len() {
        any_named_psx(entries, name, j + 1);
        assert(any_named(entries, name, (j + 1))
            == (any_named(entries, name, j)
                || entries[j].file_name@ == name));
        assert(any_named_sfx(entries, name, j)
            == (entries[j].file_name@ == name
                || any_named_sfx(entries, name, j + 1)));
    }
}

/// The per-entry recursion of the found-set scan (the slice-elem
/// field view chains at the parameter index -- probe p2; the loop
/// variable shape loses the fact in this Verus build, so the scan
/// recurses with the index as a call argument).
fn collect_step(
    entries: &[FsDirEntryFace],
    e: usize,
    custom_names: &[Vec<u8>],
    acc: (bool, bool, bool, bool, Vec<bool>),
) -> (r: (bool, bool, bool, bool, Vec<bool>))
    requires
        e <= entries.len(),
        acc.4.len() == custom_names.len(),
    ensures
        r.4.len() == custom_names.len(),
        r.0 == (acc.0
            || any_named_sfx(entries@, seq![0x2E, 0x69, 0x67, 0x6E,
                0x6F, 0x72, 0x65], e as int)),
        r.1 == (acc.1
            || any_named_sfx(entries@, seq![0x2E, 0x67, 0x69, 0x74,
                0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65], e as int)),
        r.2 == (acc.2
            || any_named_sfx(entries@, seq![0x2E, 0x67, 0x69, 0x74],
                e as int)),
        r.3 == (acc.3
            || any_named_sfx(entries@, seq![0x2E, 0x6A, 0x6A],
                e as int)),
        forall|w: int| #![trigger r.4@[w]]
            0 <= w < r.4.len() ==>
            r.4@[w] == (acc.4@[w]
                || any_named_sfx(entries@, custom_names@[w]@, e as int)),
    decreases entries.len() - e
{
    if e == entries.len() {
        return acc;
    }
    let name = entries[e].file_name.as_slice();
    let ig = ignore_lit();
    let gi = gitignore_lit();
    let dg = dot_git_lit();
    let jj = dot_jj_lit();
    let hi = acc.0 || bytes_eq(name, ig.as_slice());
    let hg = acc.1 || bytes_eq(name, gi.as_slice());
    let hd = acc.2 || bytes_eq(name, dg.as_slice());
    let hj = acc.3 || bytes_eq(name, jj.as_slice());
    let mut custom = acc.4;
    let mut q: usize = 0;
    while q < custom_names.len()
        invariant
            0 <= q <= custom_names.len(),
            custom.len() == custom_names.len(),
            forall|w: int| #![trigger custom@[w]]
                0 <= w < custom.len() ==>
                ((w < q as int ==> custom@[w]
                    == (acc.4@[w] || name@ == custom_names@[w]@))
                    && (w >= q as int ==> custom@[w] == acc.4@[w]))
        decreases custom_names.len() - q
    {
        let cname = custom_names[q].as_slice();
        if bytes_eq(name, cname) {
            custom.set(q, true);
        }
        q += 1;
    }
    proof {
        // the parameter-position field-view equation (probe p2) and
        // the suffix unfoldings it licenses (one per pool name plus
        // the per-custom name family)
        assert(name@ == entries@[e as int].file_name@);
        assert(any_named_sfx(entries@, seq![0x2E, 0x69, 0x67, 0x6E,
            0x6F, 0x72, 0x65], e as int)
            == (entries@[e as int].file_name@
                    == seq![0x2E, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65]
                || any_named_sfx(entries@, seq![0x2E, 0x69, 0x67,
                    0x6E, 0x6F, 0x72, 0x65], (e + 1) as int)));
        assert(any_named_sfx(entries@, seq![0x2E, 0x67, 0x69, 0x74,
            0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65], e as int)
            == (entries@[e as int].file_name@
                    == seq![0x2E, 0x67, 0x69, 0x74, 0x69, 0x67,
                        0x6E, 0x6F, 0x72, 0x65]
                || any_named_sfx(entries@, seq![0x2E, 0x67, 0x69,
                    0x74, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65],
                    (e + 1) as int)));
        assert(any_named_sfx(entries@, seq![0x2E, 0x67, 0x69, 0x74],
            e as int)
            == (entries@[e as int].file_name@
                    == seq![0x2E, 0x67, 0x69, 0x74]
                || any_named_sfx(entries@, seq![0x2E, 0x67, 0x69,
                    0x74], (e + 1) as int)));
        assert(any_named_sfx(entries@, seq![0x2E, 0x6A, 0x6A],
            e as int)
            == (entries@[e as int].file_name@
                    == seq![0x2E, 0x6A, 0x6A]
                || any_named_sfx(entries@, seq![0x2E, 0x6A, 0x6A],
                    (e + 1) as int)));
        assert(forall|w: int| 0 <= w < custom_names.len() ==>
            any_named_sfx(entries@, custom_names@[w]@, e as int)
                == (entries@[e as int].file_name@
                        == custom_names@[w]@
                    || any_named_sfx(entries@, custom_names@[w]@,
                        (e + 1) as int)));
    }
    collect_step(entries, e + 1, custom_names, (hi, hg, hd, hj, custom))
}

/// The exec found-set scan (upstream dir.rs:337-367, REAL): the
/// `.ignore`/`.gitignore`/`.git`/`.jj` bits and per-custom-name
/// matching over the abstract entries face (upstream reads
/// `entry.file_name()` off fs::DirEntry; the face carries the same
/// values). The public fold form is the any_named prefix; the
/// internal recursion runs the suffix form; the psx bridge connects.
pub fn collect_ignore_files(
    entries: &[FsDirEntryFace],
    custom_ignore_filenames: &[Vec<u8>],
) -> (r: IgnoreFilesFound)
    ensures
        r.custom_ignore_files.len() == custom_ignore_filenames.len(),
        r.has_ignore
            == any_named(entries@, seq![0x2E, 0x69, 0x67, 0x6E, 0x6F,
                0x72, 0x65], entries.len() as int),
        r.has_git_ignore
            == any_named(entries@, seq![0x2E, 0x67, 0x69, 0x74, 0x69,
                0x67, 0x6E, 0x6F, 0x72, 0x65], entries.len() as int),
        r.has_git_dir
            == any_named(entries@, seq![0x2E, 0x67, 0x69, 0x74],
                entries.len() as int),
        r.has_jj_dir
            == any_named(entries@, seq![0x2E, 0x6A, 0x6A],
                entries.len() as int),
        forall|q: int| #![trigger r.custom_ignore_files@[q]]
            0 <= q < r.custom_ignore_files.len() ==>
            r.custom_ignore_files@[q]
                == any_named(entries@, custom_ignore_filenames@[q]@,
                    entries.len() as int),
{
    let mut custom: Vec<bool> = Vec::new();
    let mut q0: usize = 0;
    while q0 < custom_ignore_filenames.len()
        invariant
            0 <= q0 <= custom_ignore_filenames.len(),
            custom.len() == q0,
            forall|w: int| #![trigger custom@[w]]
                0 <= w < custom.len() ==> custom@[w] == false,
        decreases custom_ignore_filenames.len() - q0
    {
        custom.push(false);
        q0 += 1;
    }
    let (hi, hg, hd, hj, custom) = collect_step(
        entries,
        0,
        custom_ignore_filenames,
        (false, false, false, false, custom),
    );
    proof {
        any_named_psx(entries@, seq![0x2E, 0x69, 0x67, 0x6E, 0x6F,
            0x72, 0x65], 0);
        any_named_psx(entries@, seq![0x2E, 0x67, 0x69, 0x74, 0x69,
            0x67, 0x6E, 0x6F, 0x72, 0x65], 0);
        any_named_psx(entries@, seq![0x2E, 0x67, 0x69, 0x74], 0);
        any_named_psx(entries@, seq![0x2E, 0x6A, 0x6A], 0);
        assert(any_named(entries@, seq![0x2E, 0x69, 0x67, 0x6E, 0x6F,
            0x72, 0x65], entries.len() as int)
            == (false
                || any_named_sfx(entries@, seq![0x2E, 0x69, 0x67,
                    0x6E, 0x6F, 0x72, 0x65], 0)));
        assert(any_named(entries@, seq![0x2E, 0x67, 0x69, 0x74, 0x69,
            0x67, 0x6E, 0x6F, 0x72, 0x65], entries.len() as int)
            == (false
                || any_named_sfx(entries@, seq![0x2E, 0x67, 0x69,
                    0x74, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65], 0)));
        assert(any_named(entries@, seq![0x2E, 0x67, 0x69, 0x74],
            entries.len() as int)
            == (false
                || any_named_sfx(entries@, seq![0x2E, 0x67, 0x69,
                    0x74], 0)));
        assert(any_named(entries@, seq![0x2E, 0x6A, 0x6A],
            entries.len() as int)
            == (false
                || any_named_sfx(entries@, seq![0x2E, 0x6A, 0x6A],
                    0)));
        assert forall|w: int| 0 <= w < custom_ignore_filenames.len() ==>
            any_named(entries@, custom_ignore_filenames@[w]@,
                entries.len() as int)
                == (false
                    || any_named_sfx(entries@,
                        custom_ignore_filenames@[w]@, 0))
        by {
            any_named_psx(entries@, custom_ignore_filenames@[w]@, 0);
        }
    }
    IgnoreFilesFound {
        has_ignore: hi,
        has_git_ignore: hg,
        has_git_dir: hd,
        has_jj_dir: hj,
        custom_ignore_files: custom,
    }
}


// ===========================================================================
// resolve_git_commondir -- upstream dir.rs:1084-1136
// ===========================================================================

/// The abstract file-read face: the outcome of one first-line read
/// (upstream io::BufReader::lines().next(), dir.rs:1107-1113 and
/// :1123-1129). OpenErr models File::open's Err arm; LineErr the
/// first line's read failure; Eof an empty stream; Line its bytes.
pub enum ReadOutcome {
    /// The file open failed.
    OpenErr,
    /// The first line read failed with an io error.
    LineErr,
    /// The stream was empty.
    Eof,
    /// The first line's bytes.
    Line(Vec<u8>),
}

/// The outcome view of resolve_git_commondir (spec tier only -- Seq
/// carriers keep the spec conversions constructible; the exec
/// Err(Some) payloads carry the io+with_path shape the Io arm
/// asserts via with_path_payload).
pub enum ResolveView {
    /// An Ok git/common dir carrier.
    Dir(Seq<u8>),
    /// The squash arm (Err(None)).
    Squash,
    /// The io arm (Err(Some(e)) with is_io and the with_path payload).
    Io(Seq<u8>),
}

/// The first-line extraction of a read face.
pub open spec fn readout_line(ro: ReadOutcome) -> Option<Seq<u8>> {
    match ro {
        ReadOutcome::OpenErr => None,
        ReadOutcome::LineErr => None,
        ReadOutcome::Eof => None,
        ReadOutcome::Line(l) => Some(l@),
    }
}

/// The exec result's view.
pub open spec fn resolve_view(r: Result<Vec<u8>, Option<Error>>)
    -> ResolveView
{
    match r {
        Ok(p) => ResolveView::Dir(p@),
        Err(None) => ResolveView::Squash,
        Err(Some(e)) => ResolveView::Io(with_path_payload(&e)),
    }
}

/// The full decision table of resolve_git_commondir (upstream
/// dir.rs:1092-1136 step for step: the gitfile gate at :1098-1100,
/// the dotgit read arms at :1101-1113, the "gitdir: " prefix check
/// and peel at :1114-1117, the commondir read arms at :1119-1129 --
/// with file2's open error squashed while file1's becomes Io-path --
/// and the relative/absolute commondir join at :1130-1134).
pub open spec fn resolve_expected(
    dir: Seq<u8>,
    git_is_file: Option<bool>,
    dotgit: ReadOutcome,
    commondir: ReadOutcome,
) -> ResolveView {
    if !(git_is_file matches Some(true)) {
        ResolveView::Dir(join_bytes(dir, seq![0x2E, 0x67, 0x69, 0x74]))
    } else {
        match dotgit {
            ReadOutcome::OpenErr => ResolveView::Io(join_bytes(dir,
                seq![0x2E, 0x67, 0x69, 0x74])),
            ReadOutcome::LineErr => ResolveView::Io(join_bytes(dir,
                seq![0x2E, 0x67, 0x69, 0x74])),
            ReadOutcome::Eof => ResolveView::Squash,
            ReadOutcome::Line(l) => {
                if !starts_with_gitdir(l@) {
                    ResolveView::Squash
                } else {
                    let rgd = strip_gitdir(l@);
                    match commondir {
                        ReadOutcome::OpenErr => ResolveView::Squash,
                        ReadOutcome::LineErr => {
                            ResolveView::Io(join_bytes(rgd,
                                commondir_spec()))
                        }
                        ReadOutcome::Eof => ResolveView::Squash,
                        ReadOutcome::Line(c) => {
                            if c@.len() > 0 && c@[0] == 0x2E {
                                ResolveView::Dir(join_bytes(rgd, c@))
                            } else {
                                ResolveView::Dir(c@)
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Find the GIT_COMMON_DIR for the given git worktree. (upstream
/// doc dir.rs:1080-1089, verbatim:
///   "This is the directory that may contain a private ignore file
///    `info/exclude`. Unlike git, this function does *not* read
///    environment variables GIT_DIR and GIT_COMMON_DIR, because it
///    is not clear how to use them when multiple repositories are
///    searched.
///    Some I/O errors are ignored.")
/// The twin parses over the abstract read faces (the fs legs ride
/// the faces); REAL body; single-equation contract via
/// resolve_expected above.
pub fn resolve_git_commondir(
    dir: &[u8],
    git_is_file: Option<bool>,
    dotgit: ReadOutcome,
    commondir: ReadOutcome,
) -> (r: Result<Vec<u8>, Option<Error>>)
    ensures resolve_view(r)
        == resolve_expected(dir@, git_is_file, dotgit, commondir),
{
    let io_face = super::IoErrorFace::new(0);
    if !(git_is_file matches Some(true)) {
        let gd = join_exec(dir, dot_git_lit().as_slice());
        return Ok(gd);
    }
    let gd_path = join_exec(dir, dot_git_lit().as_slice());
    let real_git_dir: Vec<u8>;
    match dotgit {
        ReadOutcome::OpenErr => {
            let e = super::error_with_path(
                Error::Io(io_face),
                gd_path.as_slice(),
            );
            return Err(Some(e));
        }
        ReadOutcome::LineErr => {
            let e = super::error_with_path(
                Error::Io(io_face),
                gd_path.as_slice(),
            );
            return Err(Some(e));
        }
        ReadOutcome::Eof => return Err(None),
        ReadOutcome::Line(l) => {
            if !gitdir_matches(l.as_slice()) {
                return Err(None);
            }
            real_git_dir = strip_gitdir_exec(l.as_slice());
        }
    }
    let common_path =
        join_exec(real_git_dir.as_slice(), commondir_lit().as_slice());
    match commondir {
        ReadOutcome::OpenErr => return Err(None),
        ReadOutcome::LineErr => {
            let e = super::error_with_path(
                Error::Io(io_face),
                common_path.as_slice(),
            );
            return Err(Some(e));
        }
        ReadOutcome::Eof => return Err(None),
        ReadOutcome::Line(c) => {
            if c.len() > 0 && c[0] == 0x2E {
                let joined =
                    join_exec(real_git_dir.as_slice(), c.as_slice());
                return Ok(joined);
            }
            return Ok(c);
        }
    }
}

/// The "gitdir: " prefix test (dir.rs:1114, `starts_with("gitdir: ")`).
pub open spec fn starts_with_gitdir(l: Seq<u8>) -> bool {
    l.len() >= 8
        && l[0] == 0x67
        && l[1] == 0x69
        && l[2] == 0x74
        && l[3] == 0x64
        && l[4] == 0x69
        && l[5] == 0x72
        && l[6] == 0x3A
        && l[7] == 0x20
}

/// The "commondir" literal at the spec tier.
pub open spec fn commondir_spec() -> Seq<u8> {
    seq![0x63, 0x6F, 0x6D, 0x6D, 0x6F, 0x6E, 0x64, 0x69, 0x72]
}

/// The "gitdir: " peel (dir.rs:1117: `&dot_git_line
/// ["gitdir: ".len()..]`).
pub open spec fn strip_gitdir(l: Seq<u8>) -> Seq<u8> {
    l.subrange(8, l.len() as int)
}

fn strip_gitdir_exec(l: &[u8]) -> (r: Vec<u8>)
    requires l@.len() >= 8
    ensures r@ == strip_gitdir(l@)
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 8;
    while i < l.len()
        invariant
            8 <= i <= l.len(),
            v@ == l@.subrange(8, i as int),
        decreases l.len() - i
    {
        v.push(l[i]);
        i += 1;
    }
    v
}

#[verifier::external_body]
fn gitdir_matches(l: &[u8]) -> (r: bool)
    ensures r == starts_with_gitdir(l@)
{
    unimplemented!() // trusted literal compare (the bytes_eq leg
                     // family; runtime S-rows pin the 8 bytes)
}
// ===========================================================================
// create_gitignore -- upstream dir.rs:1039-1082 (TRUSTED CONTRACT)
// ===========================================================================

/// The abstract per-(dir, names, ci) creation result (the fs reading
/// legs summarized; upstream reads each `dir_for_ignorefile/name`
/// file when it exists, collecting builder.add(gipath) io-errors via
/// maybe_push_ignore_io).
pub uninterp spec fn created_matcher_face(
    dir: Seq<u8>,
    names: Seq<Seq<u8>>,
    ci: bool,
) -> Gitignore;

/// The abstract creation error (none / the folded builder errors).
pub uninterp spec fn created_errs_face(
    dir: Seq<u8>,
    names: Seq<Seq<u8>>,
    ci: bool,
) -> Option<Error>;

/// Creates a new gitignore matcher for the directory given.
/// (upstream doc dir.rs:1039-1046, verbatim:
///   "The matcher is meant to match files below `dir`.
///    Ignore globs are extracted from each of the file names relative
///    to `dir_for_ignorefile` in the order given (earlier names have
///    lower precedence than later names).
///    I/O errors are ignored.")
/// TRUSTED CONTRACT (external_body; the file-reading legs are the
/// inventory's cut; the alignment + root + face-value posts ride
/// along so downstream gates stay concrete).
#[verifier::external_body]
pub fn create_gitignore(
    dir: &[u8],
    dir_for_ignorefile: &[u8],
    names: &[Vec<u8>],
    case_insensitive: bool,
) -> (r: (Gitignore, Option<Error>))
    requires names.len() > 0
    ensures
        r.0 == created_matcher_face(dir@, names_view(names@, 0),
            case_insensitive),
        r.1 == created_errs_face(dir_for_ignorefile@, names_view(names@, 0),
            case_insensitive),
        r.0.set.registered@.len() == r.0.globs@.len(),
        r.0.root.bytes@ == root_strip_view(dir@),
{
    unimplemented!() // trusted face: the fs reading + builder legs
}

/// The Seq-view lift of a `&[Vec<u8>]` argument (closure-free: an
/// explicit push fold, no Seq::map instantiation).
pub open spec fn names_view(ns: Seq<Vec<u8>>, k: int) -> Seq<Seq<u8>>
    decreases ns.len() - k
{
    if k >= ns.len() {
        Seq::empty()
    } else {
        names_view(ns, k + 1).push(ns[k]@)
    }
}

/// The Option<Vec<u8>> spec lift.
pub open spec fn opt_names_view(v: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match v {
        Some(x) => Some(x@),
        None => None,
    }
}

// ===========================================================================
// the add_child tier -- upstream dir.rs:264-497 (TRUSTED CONTRACT)
// ===========================================================================

/// The errs face of the add_child decision (the four create legs
/// plus the exclude-resolve error, folded root-first).
pub uninterp spec fn add_child_err_face(
    dir: Seq<u8>,
    names: Seq<Seq<u8>>,
    found_has_ignore: bool,
    found_has_git_ignore: bool,
    found_has_git_dir: bool,
    found_has_jj_dir: bool,
    found_custom: Seq<bool>,
    git_is_file: Option<bool>,
    resolved_ok: Option<Seq<u8>>,
    resolved_err: Option<Error>,
) -> Option<Error>;

/// The add_child decision table on a contract (the create legs
/// above feed the created arms; the spine's per-node consumption --
/// real-verified above -- is what carries the verdict rows).
#[verifier::external_body]
pub fn add_child_path_with_found(
    base: &Ignore,              // the callee stack (opts + names ctx)
    dir: &[u8],
    found: &IgnoreFilesFound,
    git_is_file: Option<bool>,  // the git_type probe face
    resolved_ok: Option<Vec<u8>>,   // resolve_git_commondir's Ok path
    resolved_err: Option<Error>,    // resolve_git_commondir's Err path
) -> (r: (IgnoreNode, Option<Error>))
    requires
        ig_wf(base),
        found.custom_ignore_files.len()
            == base.inner.custom_ignore_filenames.len(),
    ensures
        r.0.dir@ == dir@,
        !r.0.is_absolute_parent,
        r.0.has_absolute_parent_rules
            == base.nodes@[0].has_absolute_parent_rules,
        // the check_vcs table (dir.rs:374-375, :383-386)
        r.0.has_git == ((base.inner.opts.require_git
                && (base.inner.opts.git_ignore
                    || base.inner.opts.git_exclude))
            && (git_is_file matches Some(_)
                || (base.inner.opts.require_git
                    && (base.inner.opts.git_ignore
                        || base.inner.opts.git_exclude))
                    && found.has_jj_dir)),
        // the custom gate (dir.rs:389-419)
        (base.inner.custom_ignore_filenames.len() == 0
            || !any_found_custom(found.custom_ignore_files@))
            ==> gi_is_empty_view(&r.0.custom_ignore_matcher),
        base.inner.custom_ignore_filenames.len() > 0
            && any_found_custom(found.custom_ignore_files@)
            ==> (r.0.custom_ignore_matcher.set.registered@.len()
                    == r.0.custom_ignore_matcher.globs@.len()
                && r.0.custom_ignore_matcher.root.bytes@
                    == root_strip_view(dir@)),
        // the .ignore gate (dir.rs:420-433)
        (!base.inner.opts.ignore || !found.has_ignore)
            ==> gi_is_empty_view(&r.0.ignore_matcher),
        base.inner.opts.ignore && found.has_ignore
            ==> (r.0.ignore_matcher.set.registered@.len()
                    == r.0.ignore_matcher.globs@.len()
                && r.0.ignore_matcher.root.bytes@
                    == root_strip_view(dir@)),
        // the .gitignore gate (dir.rs:434-447)
        (!base.inner.opts.git_ignore || !found.has_git_ignore)
            ==> gi_is_empty_view(&r.0.git_ignore_matcher),
        base.inner.opts.git_ignore && found.has_git_ignore
            ==> (r.0.git_ignore_matcher.set.registered@.len()
                    == r.0.git_ignore_matcher.globs@.len()
                && r.0.git_ignore_matcher.root.bytes@
                    == root_strip_view(dir@)),
        // the exclude gate (dir.rs:449-470)
        (!base.inner.opts.git_exclude || !found.has_git_dir)
            ==> gi_is_empty_view(&r.0.git_exclude_matcher),
        base.inner.opts.git_exclude && found.has_git_dir
            && (resolved_err matches Some(_))
            ==> gi_is_empty_view(&r.0.git_exclude_matcher),
        base.inner.opts.git_exclude && found.has_git_dir
            && (resolved_err matches None)
            ==> (r.0.git_exclude_matcher.set.registered@.len()
                    == r.0.git_exclude_matcher.globs@.len()
                && r.0.git_exclude_matcher.root.bytes@
                    == root_strip_view(dir@)),
        // errs: nothing folds when every arm is closed
        (!base.inner.opts.ignore || !found.has_ignore)
            && (!base.inner.opts.git_ignore || !found.has_git_ignore)
            && (!base.inner.opts.git_exclude || !found.has_git_dir)
            && (base.inner.custom_ignore_filenames.len() == 0
                || !any_found_custom(found.custom_ignore_files@))
            && (resolved_err matches None)
            ==> r.1 matches None,
        r.1 == add_child_err_face(dir@,
            names_view(base.inner.custom_ignore_filenames@, 0),
            found.has_ignore, found.has_git_ignore, found.has_git_dir,
            found.has_jj_dir, found.custom_ignore_files@,
            git_is_file, opt_names_view(resolved_ok),
            resolved_err),
{
    unimplemented!() // trusted decision table (the four gates follow
                     // dir.rs:389-497 verbatim)
}

/// Whether any custom-ignore found bit is set (the selection bit --
/// upstream dir.rs:402-405's filter keeps names whose bit is true).
pub open spec fn any_found_custom(bits: Seq<bool>) -> bool
    decreases bits.len()
{
    bits.len() > 0
        && (bits[0] || any_found_custom(bits.subrange(1, bits.len() as int)))
}

/// The "commondir" literal (dir.rs:1118).
fn commondir_lit() -> (r: Vec<u8>)
    ensures r@ == commondir_spec()
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x63);
    v.push(0x6F);
    v.push(0x6D);
    v.push(0x6D);
    v.push(0x6F);
    v.push(0x6E);
    v.push(0x64);
    v.push(0x69);
    v.push(0x72);
    v
}


// ===========================================================================
// the add_child wrappers -- upstream dir.rs:264-330 (TRUSTED CONTRACT)
// ===========================================================================

/// The Option<Vec<u8>> None test.
pub open spec fn opt_none(v: Option<Vec<u8>>) -> bool {
    v matches None
}

/// The Option<Vec<u8>> view getter (Seq::empty on None).
pub open spec fn opt_get(v: Option<Vec<u8>>) -> Seq<u8> {
    match v {
        Some(x) => x@,
        None => Seq::empty(),
    }
}

/// Create a new `Ignore` matcher for the given child directory.
/// (upstream doc dir.rs:264-269, verbatim:
///   "Since building the matcher may require reading from multiple
///    files, it's possible that this method partially succeeds.
///    Therefore, a matcher is always returned (which may match
///    nothing) and an error is returned if it exists.
///    Note that all I/O errors are completely ignored.")
/// The twin consumes the stack (`ig`, by value: the Arc-sharing tier
/// is not value-observable); the new node becomes the chain head
/// (`nodes[0]`); the Vec-insert carries the chain rootward (the
/// `Parents` order preserved by construction).
#[verifier::external_body]
pub fn add_child(
    ig: Ignore,
    dir: &[u8],
    found: &IgnoreFilesFound,
    git_is_file: Option<bool>,
    resolved_ok: Option<Vec<u8>>,
    resolved_err: Option<Error>,
) -> (r: (Ignore, Option<Error>))
    requires
        ig_wf(&ig),
        found.custom_ignore_files.len()
            == ig.inner.custom_ignore_filenames.len(),
    ensures
        ig_wf(&r.0),
        r.0.nodes@.len() == ig.nodes@.len() + 1,
        r.0.nodes@[0].dir@ == dir@,
        !r.0.nodes@[0].is_absolute_parent,
        r.0.nodes@[0].has_absolute_parent_rules
            == ig.nodes@[0].has_absolute_parent_rules,
        r.0.nodes@[0].has_git
            == ((ig.inner.opts.require_git
                    && (ig.inner.opts.git_ignore
                        || ig.inner.opts.git_exclude))
                && ((git_is_file matches Some(_))
                    || (ig.inner.opts.require_git
                        && (ig.inner.opts.git_ignore
                            || ig.inner.opts.git_exclude))
                        && found.has_jj_dir)),
        (!ig.inner.opts.ignore || !found.has_ignore)
            ==> gi_is_empty_view(&r.0.nodes@[0].ignore_matcher),
        (!ig.inner.opts.git_ignore || !found.has_git_ignore)
            ==> gi_is_empty_view(&r.0.nodes@[0].git_ignore_matcher),
        (!ig.inner.opts.git_exclude || !found.has_git_dir)
            ==> gi_is_empty_view(&r.0.nodes@[0].git_exclude_matcher),
        (ig.inner.custom_ignore_filenames.len() == 0
            || !any_found_custom(found.custom_ignore_files@))
            ==> gi_is_empty_view(&r.0.nodes@[0].custom_ignore_matcher),
        forall|i: int| 1 <= i < r.0.nodes@.len() ==>
            (r.0.nodes@[i].dir@ == ig.nodes@[(i - 1)].dir@
                && r.0.nodes@[i].is_absolute_parent
                    == ig.nodes@[(i - 1)].is_absolute_parent
                && r.0.nodes@[i].has_absolute_parent_rules
                    == ig.nodes@[(i - 1)].has_absolute_parent_rules
                && r.0.nodes@[i].has_git
                    == ig.nodes@[(i - 1)].has_git),
        r.0.absolute_base@ == ig.absolute_base@,
{
    unimplemented!() // trusted wrapper: the add_child leg + the head
                     // insert; the tail identity above is the
                     // deferral seam for IG7's walk consumption
}

/// Like add_child, but reuse this matcher when the child adds no rules
/// or repository boundary. (upstream doc dir.rs:286-288, verbatim:
///   "Incremental matching tracks directory paths separately, so it
///    doesn't need empty nodes in the matcher chain.")
#[verifier::external_body]
pub fn add_child_with_possible_reuse(
    ig: Ignore,
    dir: &[u8],
    found: &IgnoreFilesFound,
    git_is_file: Option<bool>,
    resolved_ok: Option<Vec<u8>>,
    resolved_err: Option<Error>,
) -> (r: (Ignore, Option<Error>))
    requires
        ig_wf(&ig),
        found.custom_ignore_files.len()
            == ig.inner.custom_ignore_filenames.len(),
    ensures
        ig_wf(&r.0),
        r.0.nodes@.len() == ig.nodes@.len()
            || r.0.nodes@.len() == ig.nodes@.len() + 1,
        r.0.nodes@.len() == ig.nodes@.len()
            ==> (r.0.absolute_base@ == ig.absolute_base@
                && forall|i: int| 0 <= i < r.0.nodes@.len() ==>
                    (r.0.nodes@[i].dir@ == ig.nodes@[i].dir@
                        && !r.0.nodes@[i].has_git
                        && gi_is_empty_view(
                            &r.0.nodes@[i].custom_ignore_matcher)
                        && gi_is_empty_view(&r.0.nodes@[i].ignore_matcher)
                        && gi_is_empty_view(
                            &r.0.nodes@[i].git_ignore_matcher)
                        && gi_is_empty_view(
                            &r.0.nodes@[i].git_exclude_matcher))),
        r.0.nodes@.len() == ig.nodes@.len() + 1
            ==> (r.0.nodes@[0].dir@ == dir@
                && !r.0.nodes@[0].is_absolute_parent),
{
    unimplemented!() // trusted wrapper (the reuse gate dir.rs:294-300)
}

// ===========================================================================
// add_parents -- upstream dir.rs:191-262 (TRUSTED CONTRACT)
// ===========================================================================

/// The has_absolute_parent_rules accumulation fold (dir.rs:246-250:
/// each built node ORs in whether itself or any previously built
/// node carries ignore rules; the seed is the receiver head's flag).
pub open spec fn apf_acc(
    built: Seq<IgnoreNode>, // nodes without errors; the errs ride apf_errs
    j: int,
    seed: bool,
) -> bool
    decreases j
{
    if j <= 0 {
        seed
    } else {
        apf_acc(built, j - 1, seed)
            || !gi_is_empty_view(&built[(j - 1)].custom_ignore_matcher)
            || !gi_is_empty_view(&built[(j - 1)].ignore_matcher)
            || !gi_is_empty_view(&built[(j - 1)].git_ignore_matcher)
            || !gi_is_empty_view(&built[(j - 1)].git_exclude_matcher)
    }
}

/// The errs fold over the built parents (dir.rs:228-242: root-first
/// maybe_push per parent).
pub open spec fn apf_errs(
    built: Seq<(IgnoreNode, Option<Error>)>,
    j: int,
) -> Seq<Error>
    decreases built.len() - j
{
    if j >= built.len() {
        Seq::empty()
    } else {
        match built[j].1 {
            Some(e) => apf_errs(built, j + 1).push(e),
            None => apf_errs(built, j + 1),
        }
    }
}

/// The peb final shape (the into_error_option contract, lib.rs:398-405;
/// the plural wrap carries the stack list -- Vec view equality holds
/// element-for-element).
pub open spec fn peb_final(st: Seq<Error>) -> Option<Error> {
    if st.len() == 0 {
        None
    } else if st.len() == 1 {
        Some(st[0])
    } else {
        Some(Error::Partial(peb_vec(st)))
    }
}

/// The Vec carrier of the plural stack (spec-side; element-index
/// identity).
pub uninterp spec fn peb_vec(st: Seq<Error>) -> Vec<Error>;

/// Create a new `Ignore` matcher with the parent directories of
/// `dir`. (upstream doc dir.rs:191-194, verbatim:
///   "Note that this can only be called on an `Ignore` matcher with
///    no parents (i.e., `is_root` returns `true`). This will panic
///    otherwise.")
/// The upstream panic (dir.rs:209) is the twin's requires (the
/// documented DP5-style promise). TRUSTED CONTRACT: the built list
/// arrives root-first (canonicalize + per-parent discovery legs are
/// the faces); absolute_base attaches the canonical base (the
/// PR-3420 seam); the quirk clauses -- the has_git mask (dir.rs:245),
/// the is_absolute_parent stamp (dir.rs:243), the
/// has_absolute_parent_rules accumulation (dir.rs:246-250) -- are the
/// indexed contract below.
#[verifier::external_body]
pub fn add_parents(
    ig: Ignore,
    canonical_base: Option<Vec<u8>>,
    built: &[(IgnoreNode, Option<Error>)],
) -> (r: (Ignore, Option<Error>))
    requires
        ig_wf(&ig),
        ig.nodes.len() == 1,
        (canonical_base matches Some(_)) ==> built.len() >= 1,
    ensures
        ig_wf(&r.0),
        r.0.absolute_base@ == canonical_base@,
        r.0.nodes@.len() == built.len() + ig.nodes@.len(),
        forall|i: int| 0 <= i < built.len() ==>
            (r.0.nodes@[i].dir@
                    == built@[(built.len() - 1 - i)].0.dir@
                && r.0.nodes@[i].is_absolute_parent
                && r.0.nodes@[i].has_git
                    == (built@[(built.len() - 1 - i)].0.has_git
                        && ig.inner.opts.git_ignore)
                && r.0.nodes@[i].has_absolute_parent_rules
                    == apf_acc(apf_nodes(built@), built.len() - i,
                        ig.nodes@[0].has_absolute_parent_rules)),
        forall|i: int| built.len() <= i < r.0.nodes@.len() ==>
            (r.0.nodes@[i].dir@
                    == ig.nodes@[(i - built.len())].dir@
                && r.0.nodes@[i].is_absolute_parent
                    == ig.nodes@[(i - built.len())].is_absolute_parent
                && r.0.nodes@[i].has_absolute_parent_rules
                    == ig.nodes@[(i - built.len())]
                        .has_absolute_parent_rules),
        r.0.nodes@[r.0.nodes@.len() - 1].is_absolute_parent,
        r.1 == peb_final(apf_errs(built@, 0)),
        (forall|j: int| #![trigger built@[j].1]
            0 <= j < built.len() ==> built@[j].1 matches None)
            ==> r.1 matches None,
{
    unimplemented!() // trusted fold (the fs/cache faces carry the
                     // construction; the quirk clauses are the
                     // contract under audit)
}

/// The node-only projection of the built list.
pub open spec fn apf_nodes(built: Seq<(IgnoreNode, Option<Error>)>)
    -> Seq<IgnoreNode>
    decreases built.len()
{
    if built.len() == 0 {
        Seq::empty()
    } else {
        apf_nodes(built.subrange(1, built.len() as int)).push(
            built[built.len() - 1].0)
    }
}

// ===========================================================================
// IgnoreBuilder -- upstream dir.rs:781-1037 (REAL: setters + build)
// ===========================================================================

/// A builder for creating an Ignore matcher. (upstream struct
/// dir.rs:782-806; the twin returns () from the setters -- upstream
/// chains with &mut Self; the chaining is sugar, recorded here.)
pub struct IgnoreBuilder {
    /// The root directory path for this ignore matcher.
    pub dir: Vec<u8>,
    /// An override matcher (default is empty).
    pub overrides: Override,
    /// A type matcher (default is empty).
    pub types: Types,
    /// Explicit global ignore matchers.
    pub explicit_ignores: Vec<Gitignore>,
    /// Ignore files used in addition to .ignore.
    pub custom_ignore_filenames: Vec<Vec<u8>>,
    /// The directory that gitignores should be interpreted relative to.
    pub global_gitignores_relative_to: Option<Vec<u8>>,
    /// Ignore config.
    pub opts: IgnoreOptions,
}

/// Origin Rust (dir.rs:814-833, defaults verbatim: hidden/ignore/
/// parents/git_global/git_ignore/git_exclude enabled; ci off;
/// require_git on).
pub fn ib_new() -> (r: IgnoreBuilder)
    ensures
        types_wf(&r.types),
        r.dir@.len() == 0,
        r.explicit_ignores@.len() == 0,
        r.custom_ignore_filenames@.len() == 0,
        r.global_gitignores_relative_to matches None,
        r.opts.hidden,
        r.opts.ignore,
        r.opts.parents,
        r.opts.git_global,
        r.opts.git_ignore,
        r.opts.git_exclude,
        !r.opts.ignore_case_insensitive,
        r.opts.require_git,
{
    IgnoreBuilder {
        dir: Vec::new(),
        overrides: Override::empty(),
        types: Types::empty(),
        explicit_ignores: Vec::new(),
        custom_ignore_filenames: Vec::new(),
        global_gitignores_relative_to: None,
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

impl IgnoreBuilder {
    /// Set the current directory used for matching global gitignores
    /// (dir.rs:895-902).
    pub fn ib_current_dir(&mut self, cwd: Vec<u8>) -> ()
        requires types_wf(&self.types)
        ensures
            types_wf(&final(self).types),
            opt_get(final(self).global_gitignores_relative_to) == cwd@,
            !opt_none(final(self).global_gitignores_relative_to),
    {
        self.global_gitignores_relative_to = Some(cwd);
    }

    /// Add an override matcher (dir.rs:904-915; upstream doc "This
    /// overrides any previous setting." verbatim).
    pub fn ib_overrides(&mut self, ov: Override) -> ()
        requires types_wf(&self.types)
        ensures types_wf(&final(self).types)
    {
        self.overrides = ov;
    }

    /// Add a file type matcher (dir.rs:917-925).
    pub fn ib_types(&mut self, ty: Types) -> ()
        requires types_wf(&ty)
        ensures types_wf(&final(self).types)
    {
        self.types = ty;
    }

    /// Adds a new global ignore matcher from the ignore file path
    /// given (dir.rs:927-931) -- later adds take higher precedence at
    /// the matched_ignore explicit scan (DP25).
    pub fn ib_add_ignore(&mut self, g: Gitignore) -> ()
        requires types_wf(&self.types)
        ensures
            types_wf(&final(self).types),
            final(self).explicit_ignores@.len()
                == old(self).explicit_ignores@.len() + 1,
    {
        self.explicit_ignores.push(g);
    }

    /// Add a custom ignore file name (dir.rs:933-945, upstream doc
    /// verbatim:
    ///   "These ignore files have higher precedence than all other
    ///    ignore files.
    ///    When specifying multiple names, earlier names have lower
    ///    precedence than later names.")
    pub fn ib_add_custom_ignore_filename(&mut self, name: Vec<u8>) -> ()
        requires types_wf(&self.types)
        ensures
            types_wf(&final(self).types),
            final(self).custom_ignore_filenames@.len()
                == old(self).custom_ignore_filenames@.len() + 1,
    {
        self.custom_ignore_filenames.push(name);
    }

    /// Whether ignoring hidden files is enabled or not (dir.rs:955-958).
    pub fn ib_is_hidden(&self) -> (r: bool)
        ensures r == self.opts.hidden
    {
        self.opts.hidden
    }

    /// Enables ignoring hidden files. This is enabled by default.
    /// (dir.rs:947-953)
    pub fn ib_hidden(&mut self, yes: bool) -> ()
        requires types_wf(&self.types)
        ensures
            types_wf(&final(self).types),
            final(self).opts.hidden == yes,
    {
        self.opts.hidden = yes;
    }

    /// Enables reading `.ignore` files. This is enabled by default.
    /// (dir.rs:960-969)
    pub fn ib_ignore(&mut self, yes: bool) -> ()
        requires types_wf(&self.types)
        ensures
            types_wf(&final(self).types),
            final(self).opts.ignore == yes,
    {
        self.opts.ignore = yes;
    }

    /// Enables reading ignore files from parent directories. This is
    /// enabled by default. (dir.rs:971-980)
    pub fn ib_parents(&mut self, yes: bool) -> ()
        requires types_wf(&self.types)
        ensures
            types_wf(&final(self).types),
            final(self).opts.parents == yes,
    {
        self.opts.parents = yes;
    }

    /// Add a global gitignore matcher. Its precedence is lower than
    /// both normal `.gitignore` files and `.git/info/exclude` files.
    /// This overwrites any previous global gitignore setting. (doc
    /// dir.rs:982-993, verbatim)
    pub fn ib_git_global(&mut self, yes: bool) -> ()
        requires types_wf(&self.types)
        ensures
            types_wf(&final(self).types),
            final(self).opts.git_global == yes,
    {
        self.opts.git_global = yes;
    }

    /// Enables reading `.gitignore` files. (dir.rs:995-1004)
    pub fn ib_git_ignore(&mut self, yes: bool) -> ()
        requires types_wf(&self.types)
        ensures
            types_wf(&final(self).types),
            final(self).opts.git_ignore == yes,
    {
        self.opts.git_ignore = yes;
    }

    /// Enables reading `.git/info/exclude` files. (dir.rs:1006-1015)
    pub fn ib_git_exclude(&mut self, yes: bool) -> ()
        requires types_wf(&self.types)
        ensures
            types_wf(&final(self).types),
            final(self).opts.git_exclude == yes,
    {
        self.opts.git_exclude = yes;
    }

    /// Whether a git repository is required to apply git-related
    /// ignore rules (doc dir.rs:1017-1021, verbatim). When disabled,
    /// git-related ignore rules are applied even when searching
    /// outside a git repository.
    pub fn ib_require_git(&mut self, yes: bool) -> ()
        requires types_wf(&self.types)
        ensures
            types_wf(&final(self).types),
            final(self).opts.require_git == yes,
    {
        self.opts.require_git = yes;
    }

    /// Process ignore files case insensitively (dir.rs:1027-1036;
    /// disabled by default).
    pub fn ib_ignore_case_insensitive(&mut self, yes: bool) -> ()
        requires types_wf(&self.types)
        ensures
            types_wf(&final(self).types),
            final(self).opts.ignore_case_insensitive == yes,
    {
        self.opts.ignore_case_insensitive = yes;
    }

    /// Builds a new `Ignore` matcher using the given CWD directory.
    /// (upstream dir.rs:843-845; "The matcher returned won't match
    /// anything until ignore rules from directories are added to it.")
    /// Origin Rust (dir.rs:847-893): the global matcher is the FACE
    /// PARAMETER `ggm` -- inventory section 9: "global gitignore
    /// discovery side effects modeled as face parameters, not env
    /// reads" -- with the empty rule when the gate is off or no CWD
    /// is knowable; everything else is field transport.
    pub fn ib_build_with_cwd(
        self,
        cwd: Option<Vec<u8>>,
        ggm: &Gitignore,
    ) -> (r: Ignore)
        requires
            types_wf(&self.types),
            (cwd matches Some(_))
                ==> ggm.root.bytes@ == root_strip_view(opt_get(cwd)),
        ensures
            ig_wf(&r),
            r.nodes.len() == 1,
            r.nodes@[0].is_absolute_parent,
            !r.nodes@[0].has_git,
            !r.nodes@[0].has_absolute_parent_rules,
            r.nodes@[0].dir@.len() == 0,
            gi_is_empty_view(&r.nodes@[0].custom_ignore_matcher),
            gi_is_empty_view(&r.nodes@[0].ignore_matcher),
            gi_is_empty_view(&r.nodes@[0].git_ignore_matcher),
            gi_is_empty_view(&r.nodes@[0].git_exclude_matcher),
            r.absolute_base matches None,
            r.inner.opts.hidden == self.opts.hidden,
            r.inner.opts.ignore == self.opts.ignore,
            r.inner.opts.parents == self.opts.parents,
            r.inner.opts.git_global == self.opts.git_global,
            r.inner.opts.git_ignore == self.opts.git_ignore,
            r.inner.opts.git_exclude == self.opts.git_exclude,
            r.inner.opts.ignore_case_insensitive
                == self.opts.ignore_case_insensitive,
            r.inner.opts.require_git == self.opts.require_git,
            r.inner.custom_ignore_filenames@.len()
                == self.custom_ignore_filenames@.len(),
            r.inner.explicit_ignores@.len()
                == self.explicit_ignores@.len(),
            // the effective cwd (dir.rs:848-849: cwd or_else the field)
            (cwd matches Some(_))
                ==> opt_get(r.inner.global_gitignores_relative_to)
                    == opt_get(cwd),
            (cwd matches None
                    && opt_none(self.global_gitignores_relative_to))
                ==> opt_none(r.inner.global_gitignores_relative_to),
            (cwd matches None
                    && !opt_none(self.global_gitignores_relative_to))
                ==> opt_get(r.inner.global_gitignores_relative_to)
                    == opt_get(self.global_gitignores_relative_to),
            // the global matcher rule (dir.rs:850-867)
            (!self.opts.git_global
                || (cwd matches None
                    && self.global_gitignores_relative_to matches None))
                ==> gi_is_empty_view(&r.inner.git_global_matcher),
            self.opts.git_global && (cwd matches Some(_))
                ==> (r.inner.git_global_matcher.set.registered@.len()
                        == ggm.set.registered@.len()
                    && r.inner.git_global_matcher.globs@.len()
                        == ggm.globs@.len()
                    && r.inner.git_global_matcher.root.bytes@
                        == ggm.root.bytes@),
    {
        let empty_gg = !self.opts.git_global
            || (cwd matches None
                && self.global_gitignores_relative_to matches None);
        let eff: Option<Vec<u8>> = match cwd {
            Some(c) => Some(c),
            None => self.global_gitignores_relative_to,
        };
        let gg_final = if empty_gg {
            Gitignore::empty()
        } else {
            clone_gi(ggm)
        };
        let mut nodes: Vec<IgnoreNode> = Vec::new();
        nodes.push(IgnoreNode {
            dir: Vec::new(),
            is_absolute_parent: true,
            has_absolute_parent_rules: false,
            has_git: false,
            custom_ignore_matcher: Gitignore::empty(),
            ignore_matcher: Gitignore::empty(),
            git_ignore_matcher: Gitignore::empty(),
            git_exclude_matcher: Gitignore::empty(),
        });
        Ignore {
            inner: IgnoreInner {
                dir: self.dir,
                overrides: self.overrides,
                types: self.types,
                global_gitignores_relative_to: eff,
                explicit_ignores: self.explicit_ignores,
                custom_ignore_filenames: self.custom_ignore_filenames,
                git_global_matcher: gg_final,
                opts: self.opts,
            },
            nodes,
            absolute_base: None,
        }
    }
}

/// The deep clone of one Gitignore matcher (build_with_cwd's carrier;
/// spec-visible via the field identities below).
#[verifier::external_body]
pub fn clone_gi(g: &Gitignore) -> (r: Gitignore)
    ensures
        r.set.registered@.len() == g.set.registered@.len(),
        r.globs@.len() == g.globs@.len(),
        r.root.bytes@ == g.root.bytes@,
        r.num_ignores == g.num_ignores,
        r.num_whitelists == g.num_whitelists,
        forall|i: int| 0 <= i < g.set.registered@.len() ==>
            r.set.registered@[i].pattern@ == g.set.registered@[i].pattern@,
        forall|i: int| 0 <= i < g.set.registered@.len() ==>
            (r.set.registered@[i].case_insensitive
                == g.set.registered@[i].case_insensitive),
        forall|i: int| 0 <= i < g.globs@.len() ==>
            globs_field_view(r.globs@[i]) == globs_field_view(g.globs@[i]),
{
    unimplemented!() // trusted copy (deep via vecclone; per-index
                     // field-view identities above; runtime rows
                     // pin the identity on the built faces)
}

} // verus!

// Standalone-file invocation anchor (the harness mounts this file with
// #[path]; single-file verus runs need the empty main).
fn main() {}
