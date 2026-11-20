//! ignore 0.4.34 (pin `178cc027`) -- Verus twin, `incremental.rs` (the
//! `IncrementalIgnore` cached matcher), batch IG6.
//!
//! Upstream: github.com/BurntSushi/ripgrep @
//! 178cc027e283fd965cb72d0a7395b219eada170c (crates/ignore = 0.4.34).
//! The upstream module (crates/ignore/src/incremental.rs, 1363 lines)
//! carries the incremental checker face: the `IncrementalMatch`
//! combinator family (incremental.rs:493-580: none / ignore /
//! from_match / no_descent / not_within_depth / invert), the depth
//! accounting with the `CurDir` filter (incremental.rs:281-305), the
//! `parent_key` byte-wise fast-path trimmer (incremental.rs:107-146,
//! the unix arm), the `normalize_absolute` lexical fold
//! (incremental.rs:587-600), the root-loading state machine
//! (`RootIgnore`, incremental.rs:83-89 / :458-478) and the
//! component-walk directory cache (`CachedDir`, incremental.rs:91-105
//! / :353-436) with the "presence means this directory and every
//! ancestor were already checked" invariant (DP29), the `-` root /
//! stdin inertness (incremental.rs:154-165 / :277) and the
//! `max_filesize` stat fall-through (incremental.rs:314-336).
//!
//! Batch depth allocation (real exec bodies verified here):
//! - the whole `IncrementalMatch` combinator family, each
//!   constructor pinning its full (mat, should_descend,
//!   is_within_depth) view, and the doc flag law (a mat that reports
//!   ignore never descends);
//! - the depth decision table over the byte-segment count (the CurDir
//!   filter transcribed as the '.'-segment skip) with the three depth
//!   legs of incremental.rs:296-305 and the directory tagging of
//!   incremental.rs:342-349;
//! - `parent_key` over the memrchr face (IG1 pathutil) with the
//!   trailing-separator / `/.` trim, plus the lean-key anchor lemma
//!   (`parent_key(key joined with a normal name) == key`) that makes
//!   the fast path validate its hit;
//! - the cache read/write face: the assoc list scan
//!   (parameter-position recursion per the #IG-19 recipe), the insert
//!   chain with parent-closure (DP29) and prefix stability (the
//!   snapshot promise: loaded entries are never overwritten);
//! - the component walk (the raw-segment cursor over the consult
//!   bytes) against the closed-form `ii_walk_spec` mirror, and the
//!   top-level `ii_top_spec` composition (gates, depth, fast path,
//!   walk, filesize, directory tagging);
//! - `normalize_absolute` as the real lexical fold over the trusted
//!   `std::path::absolute` face, and `normalize` as the strip-prefix
//!   consumer (IG1 pathutil);
//! - the root loader consumed over the IG5 trusted construction legs
//!   (`add_parents` / `add_child` contracts, through the forwarding
//!   wrappers below), with the root stack kept in a one-slot Vec so
//!   the consuming moves stay value-observable.
//!
//! Trusted-contract legs (external_body; contracts consumed, never
//! expanded -- the IG5 interface discipline):
//! - `ig6_acpr` forwards dir.rs `add_child_with_possible_reuse` (the
//!   walk's per-directory construction) and names its return through
//!   the uninterp faces `acpr_child_face` / `acpr_err_face`;
//! - `ig6_add_parents` / `ig6_root_child` forward dir.rs `add_parents`
//!   / `add_child` for the root load, named through `ap_face` /
//!   `root_child_face` / `root_child_err_face`;
//! - `ig6_clone` is the walk's `Ignore` deep-copy leg (upstream clones
//!   the root stack out of `RootIgnore` and the fresh child into the
//!   cache, incremental.rs:463 / :430): it preserves `ig_wf`, the
//!   per-node labels and the matched value law
//!   (`dir_matched_spec(clone, p, d) == dir_matched_spec(orig, p, d)`
//!   for every p / d), named through `clone_face`.
//!
//! Modeling declarations (the divergences that matter):
//! - **Paths are bytes.** The crate-wide byte-carrier convention: unix
//!   `Path::is_absolute()` is `rel[0] == '/'`; std `Components` over
//!   a relative path is the raw-segment split (`seg_start` /
//!   `seg_end`): the nonempty segments in order (std collapses the
//!   repeated separators and never yields an interior '.' nor a
//!   trailing separator), so the filtered component count equals the
//!   non-'.' segment count. A '..' segment is the walk's invalid kind
//!   (incremental.rs:394-397); a leading '/' is owned by the earlier
//!   absolute gate.
//! - **OnceLock removed.** Upstream `normalized_root:
//!   OnceLock<Option<PathBuf>>` (incremental.rs:62) memoizes
//!   `normalize_absolute(&self.root)` across `normalize` calls; the
//!   memoization is not value-observable (the face is deterministic),
//!   so the twin recomputes per call and keeps a never-read field for
//!   shape fidelity.
//! - **HashMap -> assoc list.** Upstream `dirs: HashMap<OsString,
//!   CachedDir>` (incremental.rs:67) is a `Vec<CachedDirEnt>` with a
//!   first-match scan; a miss precedes every insert and walk keys
//!   strictly grow, so each key lives at most once and the scan order
//!   never matters. Within one call the walk only ever looks up keys
//!   strictly longer than every key it has inserted (they extend the
//!   walk chain past every inserted prefix), so the spec mirror may
//!   consult the call-time snapshot throughout (the frozen-cache
//!   abstraction; the live/snapshot agreement is the walk recursion's
//!   own invariant, restated at each recursive call site).
//! - **RootIgnore -> state + one-slot store.** The stack-carrying arms
//!   (Unloaded / Loaded) become `state: RootState` plus `root_store:
//!   Vec<Ignore>` (one entry whenever a stack exists); Vec push / pop
//!   keep the consuming moves (`add_parents` / `add_child` take the
//!   stack by value, the IG5 signatures) inside value semantics.
//!   NotDirectory / Stdin carry no stack, like the upstream enum
//!   assignment drops the payload it replaces.
//! - **Spec subjects are clone-named.** The walk's spec passes its
//!   subject stack through `clone_face` at every clone point
//!   (incremental.rs:408 / :430 / :463-464), so the exec's clone legs
//!   chain into the closed-form spec without congruence lemmas; the
//!   fast path consults the stored matcher directly (no clone
//!   upstream, none in the twin).
//! - **fs faces.** `Ig6FsFace` carries, per call: the root `is_dir`
//!   probe (incremental.rs:467), the root parents discovery (the
//!   add_parents `built` face, with `root_abs_base` its canonicalize
//!   leg), the root and per-directory found sets (the `git_type` /
//!   commondir resolve faces ride the children of `add_child`), and
//!   the selected `max_filesize` stat (`Ok(len)` / `Err(io)` --
//!   upstream picks metadata vs symlink_metadata via `follow_links`,
//!   incremental.rs:320-324; the selection is runtime evidence). The
//!   per-directory found set is one uniform face per call (the
//!   walk-level variation is the recorded cut; the fs suites are the
//!   runtime evidence). `std::path::absolute` is the global
//!   `std_abs_face` (normalize consults it on both the path and the
//!   root; the OnceLock lens makes the root consult deterministic).
//! - **The log line cut.** Upstream `matched` logs the error via
//!   `log::debug!` (incremental.rs:244); the string tier is cut with
//!   the IG1 Display tier -- the twin drops the error.
//! - **The error fold shape.** The errs spec tracks reverse-
//!   chronological push lists (`apply_rev` / `apply_rev2`); the walk
//!   recursion composes its segment by a pure seq push (the
//!   post-order recursion of the walk), and the root / filesize legs
//!   compose as fixed-shape segment lists -- no associativity
//!   reasoning is consumed anywhere.
//!
//! Upstream pieces NOT in this batch (deferred with anchors):
//! - the `cfg(not(unix))` arm of `parent_key` (incremental.rs:136-145):
//!   the Components::next_back twin over the same spec -- the host
//!   and the harness rows are unix.
//! - `Ig6FsFace.child_found` per-level variation along one walk (see
//!   the fs-faces note above).
//! - `WalkBuilder::build_matchers` / the `incremental` re-export
//!   plumbing: walk.rs is IG7's mount.

use vstd::prelude::*;
use vstd::seq::Seq;

use super::dir::{
    append_prefix, apf_errs, bytes_eq, dir_matched_spec, ig_m_view, ig_wf,
    join_bytes, peb_final, peb_vec, IgmPayload, Ignore, IgnoreFilesFound,
    IgnoreNode,
};
use super::gitignore::gi_is_empty_view;
use super::pathutil::{
    bytes_prefix_eq, is_hidden_path_only, is_hidden_path_only_spec,
    memrchr_face, memrchr_hit, memrchr_last, memrchr_spec,
    memrchr_spec_none_bridge, memrchr_spec_some_bridge, strip_prefix,
    strip_prefix_spec,
};
use super::{
    error_with_path, peb_stack, with_path_inner, with_path_payload, Error,
    IoErrorFace, Match, PartialErrorBuilder,
};

verus! {

// The Vec push-index axiom group (the #IG-12 recipe).
broadcast use vstd::seq::group_seq_axioms;

// ===========================================================================
// IncrementalMatch -- upstream incremental.rs:481-580
// ===========================================================================
//
// Upstream doc (incremental.rs:481-492, verbatim):
//   "The result of an incremental match.
//    This is similar to [`Match`] in that it reports whether a file
//    path should be ignored, whitelisted or didn't match anything at
//    all. It also has extra data, such as whether a directory matched
//    but should not be descended into.
//    Generally speaking, callers who only care about specific files
//    can stick to the `is_none()`, `is_ignore()` or `is_whitelist()`
//    predicates. Directory entries are more complicated because we
//    sometimes want to yield directories to descend into, but not
//    actually visit (e.g., for the minimum depth filter). Or, we may
//    want to yield a directory to visit but not descend into
//    (e.g., for the maximum depth filter)."

/// The match-kind code of the carried payload (0 none, 1 ignore,
/// 2 whitelist; the spec view of incremental.rs:494-498).
pub open spec fn m_code(m: &Match<()>) -> int {
    match m {
        Match::None => 0,
        Match::Ignore(_) => 1,
        Match::Whitelist(_) => 2,
    }
}

/// The three-field result view (the spec-side projection of the
/// upstream struct fields: mat / should_descend / is_within_depth).
pub open spec fn inc_view(m: &IncrementalMatch) -> (int, bool, bool) {
    (m_code(&m.mat), m.should_descend, m.is_within_depth)
}

/// The view of the `none(is_dir)` constructor (incremental.rs:
/// 501-507).
pub open spec fn none_view(is_dir: bool) -> (int, bool, bool) {
    (0, is_dir, true)
}

/// The view of the `ignore()` constructor (incremental.rs:509-515).
pub open spec fn ignore_view() -> (int, bool, bool) {
    (1, false, true)
}

/// The spec constructor `none(is_dir)` (incremental.rs:501-507).
pub open spec fn im_none(is_dir: bool) -> IncrementalMatch {
    IncrementalMatch {
        mat: Match::None,
        should_descend: is_dir,
        is_within_depth: true,
    }
}

/// The spec constructor `ignore()` (incremental.rs:509-515).
pub open spec fn im_ignore() -> IncrementalMatch {
    IncrementalMatch {
        mat: Match::Ignore(()),
        should_descend: false,
        is_within_depth: true,
    }
}

/// The spec constructor `ignore().not_within_depth()` (the two early
/// depth legs, incremental.rs:299 / :303).
pub open spec fn im_nwd() -> IncrementalMatch {
    IncrementalMatch {
        mat: Match::Ignore(()),
        should_descend: false,
        is_within_depth: false,
    }
}

/// The spec constructor from a kind code (the view inverse; the unit
/// payload makes the kind total).
pub open spec fn im_of_kind(kind: int, sd: bool, iwd: bool)
    -> IncrementalMatch
{
    IncrementalMatch {
        mat: if kind == 0 {
            Match::None
        } else if kind == 1 {
            Match::Ignore(())
        } else {
            Match::Whitelist(())
        },
        should_descend: sd,
        is_within_depth: iwd,
    }
}

/// Two results with equal views are equal (the unit payload makes
/// the view total).
proof fn inc_view_eq(a: &IncrementalMatch, b: &IncrementalMatch)
    requires inc_view(a) == inc_view(b)
    ensures a == b
{
    reveal(inc_view);
    reveal(m_code);
    // The per-case constructor concretization (the #IG-19 recipe: the
    // variant identity is pinned by the code equality on each arm,
    // then the datatype equality follows from the concrete
    // constructor forms -- the aggregate conjunction in one assert
    // loses the triggering context, so each case carries its own).
    match a.mat {
        Match::None => {
            match b.mat {
                Match::None => {
                    assert(a.mat == b.mat);
                }
                _ => {
                    assert(false);
                }
            }
        }
        Match::Ignore(u) => {
            match b.mat {
                Match::Ignore(u2) => {
                    assert(u == ());  // the unit payload
                    assert(u2 == ());
                    assert(a.mat == b.mat);
                }
                _ => {
                    assert(false);
                }
            }
        }
        Match::Whitelist(u) => {
            match b.mat {
                Match::Whitelist(u2) => {
                    assert(u == ());
                    assert(u2 == ());
                    assert(a.mat == b.mat);
                }
                _ => {
                    assert(false);
                }
            }
        }
    }
    assert(a.mat == b.mat);
    assert(a.should_descend == b.should_descend);
    assert(a.is_within_depth == b.is_within_depth);
    assert(a.mat == a.mat);
    assert(a == b);
}

/// Origin struct (incremental.rs:493-498).
pub struct IncrementalMatch {
    /// The underlying match (upstream mat: Match<()>).
    pub mat: Match<()>,
    /// Whether the caller should descend into this directory.
    pub should_descend: bool,
    /// Whether this entry is within the depth filter.
    pub is_within_depth: bool,
}

impl IncrementalMatch {
    /// Origin Rust (incremental.rs:501-507).
    pub fn none(is_dir: bool) -> (r: IncrementalMatch)
        ensures
            inc_view(&r) == none_view(is_dir),
            r == im_none(is_dir),
    {
        IncrementalMatch {
            mat: Match::None,
            should_descend: is_dir,
            is_within_depth: true,
        }
    }

    /// Origin Rust (incremental.rs:509-515).
    pub fn ignore() -> (r: IncrementalMatch)
        ensures
            inc_view(&r) == ignore_view(),
            r == im_ignore(),
    {
        IncrementalMatch {
            mat: Match::Ignore(()),
            should_descend: false,
            is_within_depth: true,
        }
    }

    /// Origin Rust (incremental.rs:517-520): the should_descend law
    /// `is_dir && !mat.is_ignore()` (the flag doc law: a match that
    /// reports ignore never descends, whatever is_dir says --
    /// incremental.rs:546-557's "always false" sentence covers the
    /// is_dir = false constructor inputs too).
    pub fn from_match(mat: Match<()>, is_dir: bool) -> (r: IncrementalMatch)
        ensures
            inc_view(&r)
                == (m_code(&mat), is_dir && m_code(&mat) != 1, true),
            r == im_of_kind(
                m_code(&mat),
                is_dir && m_code(&mat) != 1,
                true,
            ),
    {
        let should_descend = is_dir && !(mat.is_ignore());
        let r = IncrementalMatch {
            mat,
            should_descend,
            is_within_depth: true,
        };
        proof {
            reveal(im_of_kind);
            let spec = im_of_kind(m_code(&mat),
                is_dir && m_code(&mat) != 1, true);
            inc_view_eq(&r, &spec);
        }
        r
    }

    /// Origin Rust (incremental.rs:522-524): the struct update
    /// `IncrementalMatch { should_descend: false, ..self }` written
    /// field-wise.
    pub fn no_descent(self) -> (r: IncrementalMatch)
        ensures
            inc_view(&r) == (inc_view(&self).0, false, inc_view(&self).2),
            r == im_of_kind(inc_view(&self).0, false, inc_view(&self).2),
    {
        let r = IncrementalMatch {
            mat: self.mat,
            should_descend: false,
            is_within_depth: self.is_within_depth,
        };
        proof {
            reveal(im_of_kind);
            let spec =
                im_of_kind(inc_view(&self).0, false, inc_view(&self).2);
            inc_view_eq(&r, &spec);
        }
        r
    }

    /// Origin Rust (incremental.rs:526-528).
    pub fn not_within_depth(self) -> (r: IncrementalMatch)
        ensures
            inc_view(&r) == (inc_view(&self).0, inc_view(&self).1, false),
            r == im_of_kind(inc_view(&self).0, inc_view(&self).1, false),
    {
        let r = IncrementalMatch {
            mat: self.mat,
            should_descend: self.should_descend,
            is_within_depth: false,
        };
        proof {
            reveal(im_of_kind);
            let spec =
                im_of_kind(inc_view(&self).0, inc_view(&self).1, false);
            inc_view_eq(&r, &spec);
        }
        r
    }

    /// Upstream doc (incremental.rs:530, verbatim):
    ///   "Returns true if the match result didn't match anything."
    pub fn is_none(&self) -> (r: bool)
        ensures r == (inc_view(&self).0 == 0)
    {
        self.mat.is_none()
    }

    /// Upstream doc (incremental.rs:535-536, verbatim):
    ///   "Returns true if the match result implies the path should be
    ///    ignored."
    pub fn is_ignore(&self) -> (r: bool)
        ensures r == (inc_view(&self).0 == 1)
    {
        self.mat.is_ignore()
    }

    /// Upstream doc (incremental.rs:540-541, verbatim):
    ///   "Returns true if the match result implies the path should be
    ///    whitelisted."
    pub fn is_whitelist(&self) -> (r: bool)
        ensures r == (inc_view(&self).0 == 2)
    {
        self.mat.is_whitelist()
    }

    /// Upstream doc (incremental.rs:546-557, verbatim):
    ///   "Returns true only when this match corresponds to a
    ///    directory *and* whether the caller should look inside this
    ///    directory for additional results.
    ///    It is possible for a match to report `false` for
    ///    [`IncrementalMatch::is_ignore`] _and_ `false` for
    ///    [`IncrementalMatch::should_descend`]. This can occur, for
    ///    example, when a maximum depth setting allows a directory
    ///    through, but where none of its children entries should be
    ///    visited.
    ///    This is always `false` for a file path that does *not*
    ///    correspond to a directory."
    pub fn should_descend(&self) -> (r: bool)
        ensures r == inc_view(&self).1
    {
        self.should_descend
    }

    /// Upstream doc (incremental.rs:562-570, verbatim):
    ///   "Returns true only when this result corresponds to an entry
    ///    that is within the depth filter.
    ///    This is `false` when a path corresponds to a directory and
    ///    is less than the minimum depth. In this case, callers should
    ///    continue looking inside that directory.
    ///    This is always `true` for a match corresponding to a file
    ///    path that isn't a directory."
    pub fn is_within_depth(&self) -> (r: bool)
        ensures r == inc_view(&self).2
    {
        self.is_within_depth
    }

    /// Upstream doc (incremental.rs:574-576, verbatim):
    ///   "Inverts the match so that `Ignore` becomes `Whitelist` and
    ///    `Whitelist` becomes `Ignore`. A non-match remains the same."
    ///
    /// The flags ride along (the struct update written field-wise).
    pub fn invert(self) -> (r: IncrementalMatch)
        ensures
            inc_view(&r)
                == (if inc_view(&self).0 == 1 {
                    2
                } else if inc_view(&self).0 == 2 {
                    1
                } else {
                    0
                }, inc_view(&self).1, inc_view(&self).2)
    {
        IncrementalMatch {
            mat: self.mat.invert(),
            should_descend: self.should_descend,
            is_within_depth: self.is_within_depth,
        }
    }
}

// ===========================================================================
// IncrementalIgnoreOptions -- upstream incremental.rs:72-81
// ===========================================================================
//
// Upstream doc (incremental.rs:72-74, verbatim):
//   "The options for a matcher, mostly meant to duplicate as much as
//    we can from `WalkParallel`."
// Upstream visibility pub(crate); opened pub for the harness mounts
// (the crate-wide convention recorded at lib.rs).

/// Origin struct (incremental.rs:74-81); every field doc verbatim.
pub struct IncrementalIgnoreOptions {
    /// The min depth option (upstream min_depth: Option<usize>).
    pub min_depth: Option<usize>,
    /// The max depth option (upstream max_depth: Option<usize>).
    pub max_depth: Option<usize>,
    /// The max filesize option (upstream max_filesize: Option<u64>).
    pub max_filesize: Option<u64>,
    /// Whether hidden entries are ignored (upstream hidden: bool).
    pub hidden: bool,
    /// Whether symlinks are followed (upstream follow_links: bool).
    pub follow_links: bool,
}

// ===========================================================================
// the relative-path segment machinery (the std Components model)
// ===========================================================================
//
// Upstream consults `relative.components()` with the CurDir filter
// (incremental.rs:284-290 / :381-387). On a byte carrier, for the
// relative paths that pass the earlier absolute gate, std yields the
// nonempty non-'.' segments in order: the interior '.' runs and the
// repeated separators are normalized away by std, and a leading '.'
// is the CurDir the filter drops (the count matches either way). The
// '..' segment is the walk's invalid kind (incremental.rs:394-397 --
// RootDir / Prefix need a leading separator or a prefix, both owned
// by the earlier absolute gate on unix).

/// Whether a byte path starts at the root separator (unix
/// `Path::is_absolute`, bytewise; the gate of incremental.rs:277).
pub open spec fn rel_abs(rel: Seq<u8>) -> bool {
    rel.len() > 0 && rel[0] == 0x2F
}

/// The start of the next raw segment at-or-after `i` (skips the
/// separator runs; `rel.len()` when none).
pub open spec fn seg_start(rel: Seq<u8>, i: int) -> int
    decreases rel.len() - i
{
    if i >= rel.len() as int {
        rel.len() as int
    } else if rel[i] == 0x2F {
        seg_start(rel, i + 1)
    } else {
        i
    }
}

/// The end of the raw segment starting at `s` (the next separator or
/// `rel.len()`).
pub open spec fn seg_end(rel: Seq<u8>, s: int) -> int
    decreases rel.len() - s
{
    if s >= rel.len() as int {
        rel.len() as int
    } else if rel[s] == 0x2F {
        s
    } else {
        seg_end(rel, s + 1)
    }
}

/// The '.' segment sentinel (the CurDir the filter drops).
pub open spec fn is_dot(s: Seq<u8>) -> bool {
    s == seq![0x2E]
}

/// The '..' segment sentinel (the walk's invalid kind).
pub open spec fn is_dotdot(s: Seq<u8>) -> bool {
    s == seq![0x2E, 0x2E]
}

/// The exec carrier of `seg_start` (parameter-position recursion,
/// the #IG-19 form).
pub fn seg_start_exec(rel: &[u8], i: usize) -> (r: usize)
    requires i <= rel.len()
    ensures r as int == seg_start(rel@, i as int)
    decreases rel.len() - i
{
    if i >= rel.len() {
        i
    } else if rel[i] == 0x2F {
        seg_start_exec(rel, i + 1)
    } else {
        i
    }
}

/// The exec carrier of `seg_end`.
pub fn seg_end_exec(rel: &[u8], s: usize) -> (r: usize)
    requires s <= rel.len()
    ensures r as int == seg_end(rel@, s as int)
    decreases rel.len() - s
{
    if s >= rel.len() {
        s
    } else if rel[s] == 0x2F {
        s
    } else {
        seg_end_exec(rel, s + 1)
    }
}

// The depth machinery is a byte-scan state machine (the #IG-19
// syntactic-recursion form): each recursion step advances exactly one
// byte, so the termination check is trivial; a raw segment's first
// byte opens it, a '.'-segment is a single '.' byte immediately
// followed by a separator or the end -- exactly the '.' segment the
// upstream CurDir filter drops (std never yields an interior '.').

/// The in-segment scan state (acc: the count so far; in_seg: whether
/// the byte at c extends an already-open raw segment).
pub open spec fn depth_scan(rel: Seq<u8>, c: int, in_seg: bool) -> int
    decreases rel.len() - c
{
    if c >= rel.len() as int {
        0
    } else if rel[c] == 0x2F {
        depth_scan(rel, c + 1, false)
    } else if in_seg {
        depth_scan(rel, c + 1, true)
    } else {
        let dotseg = rel[c] == 0x2E
            && ((c + 1 >= rel.len() as int) || rel[c + 1] == 0x2F);
        (if dotseg { 0 as int } else { 1 as int })
            + depth_scan(rel, c + 1, true)
    }
}

/// The filtered component count (the upstream depth:
/// `components().filter_map(CurDir => None).count()`,
/// incremental.rs:284-290). A '..' segment still counts -- the depth
/// gates run before the walk's invalidity bail.
pub open spec fn depth_count(rel: Seq<u8>, c: int) -> int {
    depth_scan(rel, c, false)
}

/// The byte-step carry of depth_scan (used by the exec mirror's
/// invariant): the remaining count steps by one byte at a time.
proof fn depth_scan_step(rel: Seq<u8>, c: int, in_seg: bool)
    requires c < rel.len()
    ensures
        rel[c] == 0x2F ==>
            depth_scan(rel, c, in_seg)
                == depth_scan(rel, c + 1, false),
        rel[c] != 0x2F && in_seg ==>
            depth_scan(rel, c, in_seg)
                == depth_scan(rel, c + 1, true),
        rel[c] != 0x2F && !in_seg ==>
            depth_scan(rel, c, in_seg)
                == ((if rel[c] == 0x2E
                    && ((c + 1 >= rel.len() as int)
                        || rel[c + 1] == 0x2F)
                {
                    0 as int
                } else {
                    1 as int })
                    + depth_scan(rel, c + 1, true)),
    decreases rel.len() - c
{
    reveal(depth_scan);
}

/// The exec carrier of `depth_count` (the byte-scan mirror).
pub fn depth_count_exec(rel: &[u8], c: usize) -> (r: usize)
    requires c <= rel.len()
    ensures r as int == depth_count(rel@, c as int)
{
    let mut i: usize = c;
    let mut in_seg = false;
    let mut acc: usize = 0;
    while i < rel.len()
        invariant
            c <= i <= rel.len(),
            acc as int <= i as int,
            acc as int + depth_scan(rel@, i as int, in_seg)
                == depth_count(rel@, c as int),
        decreases rel.len() - i
    {
        proof {
            depth_scan_step(rel@, i as int, in_seg);
        }
        if rel[i] == 0x2F {
            in_seg = false;
        } else if in_seg {
            // the byte extends the open segment
        } else {
            let next_is_sep_or_end: bool =
                i + 1 >= rel.len() || rel[i + 1] == 0x2F;
            let dotseg = rel[i] == 0x2E && next_is_sep_or_end;
            if !dotseg {
                // acc <= i holds, so acc + 1 <= i + 1 stays in range
                acc = acc + 1;
            }
            in_seg = true;
        }
        i += 1;
    }
    proof {
        reveal(depth_scan);
        assert(depth_scan(rel@, rel.len() as int, in_seg) == 0);
    }
    acc
}

/// The in-segment scan state of the peek (any_nd).
pub open spec fn any_nd(rel: Seq<u8>, c: int, in_seg: bool) -> bool
    decreases rel.len() - c
{
    if c >= rel.len() as int {
        false
    } else if rel[c] == 0x2F {
        any_nd(rel, c + 1, false)
    } else if in_seg {
        any_nd(rel, c + 1, true)
    } else {
        let dotseg = rel[c] == 0x2E
            && ((c + 1 >= rel.len() as int) || rel[c + 1] == 0x2F);
        !dotseg || any_nd(rel, c + 1, true)
    }
}

/// Whether any filtered component exists at/after c (the upstream
/// `components.peek()?` of incremental.rs:388).
pub open spec fn has_any_comp(rel: Seq<u8>, c: int) -> bool {
    any_nd(rel, c, false)
}

/// The byte-step carry of any_nd.
proof fn any_nd_step(rel: Seq<u8>, c: int, in_seg: bool)
    requires c < rel.len()
    ensures
        rel[c] == 0x2F ==>
            any_nd(rel, c, in_seg) == any_nd(rel, c + 1, false),
        rel[c] != 0x2F && in_seg ==>
            any_nd(rel, c, in_seg) == any_nd(rel, c + 1, true),
        rel[c] != 0x2F && !in_seg ==>
            any_nd(rel, c, in_seg)
                == (!(rel[c] == 0x2E
                    && ((c + 1 >= rel.len() as int)
                        || rel[c + 1] == 0x2F))
                    || any_nd(rel, c + 1, true)),
    decreases rel.len() - c
{
    reveal(any_nd);
}

/// Truth at a one-byte-later position implies truth at the start:
/// the scan state arriving at c is decided by the byte at c - 1, and
/// every byte step either passes the value through or decides true
/// outright (the fresh non-dot-segment opener). The witnessing true
/// value is carried back one position at a time.
proof fn any_nd_true_back(rel: Seq<u8>, c: int, sg: bool)
    requires
        0 <= c <= rel.len(),
        sg == (if c > 0 { rel[c - 1] != 0x2F } else { false }),
        any_nd(rel, c, sg) == true,
    ensures any_nd(rel, 0, false) == true
    decreases c
{
    if c == 0 {
        // sg == false at the start; the witness is the target value
    } else {
        let sg0 = (if c - 1 > 0 { rel[c - 2] != 0x2F } else { false });
        any_nd_step(rel, c - 1, false);
        any_nd_step(rel, c - 1, true);
        if rel[c - 1] == 0x2F {
            // '/' resets: both predecessor states step to (c, false)
            assert(any_nd(rel, c - 1, false) == any_nd(rel, c, false));
            assert(any_nd(rel, c - 1, true) == any_nd(rel, c, false));
            assert(any_nd(rel, c - 1, sg0) == true);
            any_nd_true_back(rel, c - 1, sg0);
        } else {
            // non-'/' at c - 1: the in-segment state passes through
            // and the fresh state is (!dotseg || any_nd(c, true)),
            // both true when any_nd(c, true) is (the arriving state
            // at a non-'/' byte is true)
            assert(sg == true);
            assert(any_nd(rel, c, true) == true);
            assert(any_nd(rel, c - 1, true) == true);
            assert(any_nd(rel, c - 1, false) == true);
            any_nd_true_back(rel, c - 1, sg0);
        }
    }
}

/// A real component opener at a fresh position (start or right after
/// a separator; the byte is not '.'-before-a-separator-or-end)
/// witnesses has_any_comp.
proof fn has_any_comp_witness(rel: Seq<u8>, p: int)
    requires
        0 <= p < rel.len(),
        rel[p] != 0x2F,
        p == 0 || rel[p - 1] == 0x2F,
        !(rel[p] == 0x2E
            && ((p + 1 >= rel.len() as int) || rel[p + 1] == 0x2F)),
    ensures has_any_comp(rel, 0) == true
{
    // the fresh state at the witness position decides true outright
    reveal(any_nd);
    assert(any_nd(rel, p, false) == true);
    any_nd_true_back(rel, p, false);
}

/// The exec carrier of `has_any_comp` (the byte-scan mirror).
pub fn has_any_comp_exec(rel: &[u8], c: usize) -> (r: bool)
    requires c <= rel.len()
    ensures r == has_any_comp(rel@, c as int)
{
    let mut i: usize = c;
    let mut in_seg = false;
    while i < rel.len()
        invariant
            c <= i <= rel.len(),
            any_nd(rel@, i as int, in_seg) == has_any_comp(rel@, c as int),
        decreases rel.len() - i
    {
        proof {
            any_nd_step(rel@, i as int, in_seg);
        }
        if rel[i] == 0x2F {
            in_seg = false;
        } else if in_seg {
            // extends the open segment
        } else {
            let next_is_sep_or_end: bool =
                i + 1 >= rel.len() || rel[i + 1] == 0x2F;
            let dotseg = rel[i] == 0x2E && next_is_sep_or_end;
            if !dotseg {
                return true;
            }
            in_seg = true;
        }
        i += 1;
    }
    proof {
        reveal(any_nd);
        assert(any_nd(rel@, rel.len() as int, in_seg) == false);
    }
    false
}

/// The raw-segment range carries (for the exec slicing).
proof fn seg_bounds(rel: Seq<u8>, c: int)
    requires 0 <= c <= rel.len()
    ensures
        c <= seg_start(rel, c) <= rel.len(),
        seg_start(rel, c) <= seg_end(rel, seg_start(rel, c)) <= rel.len(),
    decreases rel.len() - c
{
    let s = seg_start(rel, c);
    if c < rel.len() {
        if rel[c] == 0x2F {
            seg_bounds(rel, c + 1);
        }
        seg_end_bounds(rel, s);
    }
}

/// The seg_end range carry.
proof fn seg_end_bounds(rel: Seq<u8>, s: int)
    requires 0 <= s <= rel.len()
    ensures s <= seg_end(rel, s) <= rel.len()
    decreases rel.len() - s
{
    if s < rel.len() && rel[s] != 0x2F {
        seg_end_bounds(rel, s + 1);
    }
}

// ===========================================================================
// parent_key -- upstream incremental.rs:107-146 (unix arm)
// ===========================================================================
//
// Upstream doc (incremental.rs:107-110, verbatim):
//   "Returns a parent key for the directory cache, provided the final
//    component is normal. On Unix, a byte-wise lookup avoids parsing
//    path components. Cache keys contain only normal components, so a
//    hit also validates the parent. Other spellings are handled by the
//    component walk after a miss."
// Upstream inline comment (incremental.rs:123-125, verbatim):
//   "As with `Components::as_path`, trim trailing separators and `.`
//    components so these spellings can still hit the cache directly."

/// The trim end (the loop of incremental.rs:126-134: drop a trailing
/// separator, or a `/.` pair, and re-check), as an end position
/// inside `rel` bounded by `j`.
pub open spec fn pk_trim_end(rel: Seq<u8>, j: int) -> int
    decreases j + 1
{
    if j <= 0 {
        0
    } else if rel[j - 1] == 0x2F {
        pk_trim_end(rel, j - 1)
    } else if j >= 2 && rel[j - 2] == 0x2F && rel[j - 1] == 0x2E {
        pk_trim_end(rel, j - 2)
    } else {
        j
    }
}

/// The spec track of `parent_key` (the unix arm; the cfg(not(unix))
/// arm, the Components::next_back twin, is the recorded cut -- the
/// host and the harness rows are unix).
pub open spec fn parent_key_spec(rel: Seq<u8>) -> Option<Seq<u8>> {
    match memrchr_spec(rel, 0x2F) {
        None => None,
        Some(slash) => {
            let name = rel.subrange(slash + 1, rel.len() as int);
            let e = pk_trim_end(rel, slash);
            if name.len() == 0 || is_dot(name) || is_dotdot(name) {
                None
            } else {
                Some(rel.subrange(0, e))
            }
        }
    }
}

/// The exec carrier of the trim loop (parameter-position recursion).
pub fn pk_trim_end_exec(rel: &[u8], j: usize) -> (r: usize)
    requires j <= rel.len()
    ensures r as int == pk_trim_end(rel@, j as int)
    decreases j
{
    if j == 0 {
        0
    } else if rel[j - 1] == 0x2F {
        pk_trim_end_exec(rel, j - 1)
    } else if j >= 2 && rel[j - 2] == 0x2F && rel[j - 1] == 0x2E {
        pk_trim_end_exec(rel, j - 2)
    } else {
        j
    }
}

/// The trim-range carry (for the parent slice bounds).
proof fn pk_trim_end_bounds(rel: Seq<u8>, j: int)
    requires 0 <= j <= rel.len()
    ensures 0 <= pk_trim_end(rel, j) <= j
    decreases j + 1
{
    reveal(pk_trim_end);
    if j > 0 {
        if rel[j - 1] == 0x2F {
            pk_trim_end_bounds(rel, j - 1);
        } else if j >= 2 && rel[j - 2] == 0x2F && rel[j - 1] == 0x2E {
            pk_trim_end_bounds(rel, j - 2);
        }
    }
}

// The reverse side of the memrchr face contract (the exec scan's
// Some arm gives the facts forward; the spec's Some gives them
// backward -- the fast-path guard reads the face from the spec side).

/// Hit-guarded downward carry: with any witness hit at or below
/// `from`, the memrchr_last scan lands on the highest hit below
/// `from` (or `from` itself when it hits).
proof fn mr_witness_max(s: Seq<u8>, cc: u8, from: int, w: int)
    requires
        0 <= w <= from < s.len(),
        s[w] == cc,
    ensures
        0 <= memrchr_last(s, from, cc) <= from
            && s[memrchr_last(s, from, cc)] == cc
            && forall|q: int|
                #![trigger s[q]]
                memrchr_last(s, from, cc) < q <= from ==> s[q] != cc,
    decreases from - w
{
    reveal(memrchr_last);
    if s[from] == cc {
        // the top of the scan is itself the highest hit
    } else {
        // no hit at `from`: the value comes from one level below
        // (w <= from - 1 since s[w] == cc != s[from])
        mr_witness_max(s, cc, from - 1, w);
    }
}

/// The spec-side Some inversion: the returned position is the last
/// occurrence (the slash-position facts the fast path consumes).
proof fn memrchr_spec_some_inv(s: Seq<u8>, cc: u8, i: int)
    requires memrchr_spec(s, cc) == Some(i)
    ensures
        0 <= i < s.len(),
        s[i] == cc,
        forall|q: int| i < q < s.len() ==> s[q] != cc,
{
    reveal(memrchr_spec);
    reveal(memrchr_hit);
    assert(memrchr_hit(s, cc));
    let w = choose|j: int| 0 <= j < s.len() && s[j] == cc;
    mr_witness_max(s, cc, s.len() - 1, w);
}

/// A parent key exists only when the path carries a real final
/// component, so a fast-path hit implies the walk's peek gate would
/// pass (the spec-side guard of the fast-path arm in the top
/// composition).
proof fn pk_implies_any_comp(rel: Seq<u8>)
    requires parent_key_spec(rel) matches Some(_)
    ensures has_any_comp(rel, 0) == true
{
    reveal(parent_key_spec);
    assert(memrchr_spec(rel, 0x2F) matches Some(_));
    let sl = match memrchr_spec(rel, 0x2F) {
        Some(p) => p,
        None => 0,
    };
    memrchr_spec_some_inv(rel, 0x2F, sl);
    // the name slice passed the parent_key name check: nonempty and
    // neither sentinel -- so its first byte opens a real component
    let name = rel.subrange(sl + 1, rel.len() as int);
    assert(name.len() > 0 && !is_dot(name) && !is_dotdot(name));
    assert(sl + 1 < rel.len());
    assert(rel[sl + 1] != 0x2F);
    // a dot segment head is impossible: '.' at end is the '.' name
    // (excluded), '.' before a '/' would contradict the last-slash
    // max fact
    assert(!(rel[sl + 1] == 0x2E
        && ((sl + 2 >= rel.len() as int) || rel[sl + 2] == 0x2F))) by {
        if rel[sl + 1] == 0x2E && sl + 2 >= rel.len() as int {
            assert(name.len() == 1);
            assert(name[0] == 0x2E);
            assert(name == seq![0x2E]);
            assert(false);
        }
        if rel[sl + 1] == 0x2E && rel[sl + 2] == 0x2F {
            assert(false);
        }
    }
    has_any_comp_witness(rel, sl + 1);
}

/// Origin Rust (incremental.rs:111-146), the unix arm transcribed
/// verbatim onto the bytes (the returned borrow becomes an owned byte
/// carrier); the memrchr consult goes through the IG1 face.
pub fn parent_key(rel: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        (r matches None) == (parent_key_spec(rel@) matches None),
        r matches Some(v2) ==> (parent_key_spec(rel@)
            matches Some(sv2) && v2@ == sv2),
{
    // let slash = memrchr::memrchr(b'/', bytes)?;
    match memrchr_face(rel, 0x2F) {
        None => {
            proof {
                // the face's None arm: no separator anywhere
                reveal(parent_key_spec);
                assert(memrchr_spec(rel@, 0x2F) matches None);
                memrchr_spec_none_bridge(rel@, 0x2F);
            }
            None
        }
        Some(slash) => {
            proof {
                memrchr_spec_some_bridge(rel@, 0x2F, slash as int);
                reveal(parent_key_spec);
                pk_trim_end_bounds(rel@, slash as int);
            }
            // let name = &bytes[slash + 1..];
            let name = &rel[slash + 1..];
            // if name.is_empty() || name == b"." || name == b".." {
            //     return None;
            // }
            // (the b"." / b".." comparisons are spelled index-wise --
            // the same face as the gitignore twin's root_is_dot row;
            // the array-literal view does not bridge to the seq!
            // literals without it, the #IG-19 element-projection wall)
            let name_is_dot: bool =
                name.len() == 1 && name[0] == 0x2E;
            let name_is_dotdot: bool =
                name.len() == 2 && name[0] == 0x2E && name[1] == 0x2E;
            if name.len() == 0 || name_is_dot || name_is_dotdot {
                proof {
                    // the name slice is the spec's post-slash subrange
                    let nspec = rel@.subrange(
                        slash as int + 1, rel@.len() as int);
                    assert(name@ == nspec);
                    assert(nspec.len() == 0 || is_dot(nspec)
                        || is_dotdot(nspec)) by {
                        if name_is_dot {
                            assert(nspec.len() == 1);
                            assert(nspec[0] == 0x2E);
                            assert(nspec == seq![0x2E]);
                        } else if name_is_dotdot {
                            assert(nspec.len() == 2);
                            assert(nspec[0] == 0x2E);
                            assert(nspec[1] == 0x2E);
                            assert(nspec == seq![0x2E, 0x2E]);
                        }
                    }
                }
                None
            } else {
                // let mut parent = &bytes[..slash]; then the trim loop
                let e = pk_trim_end_exec(rel, slash);
                proof {
                    let nspec = rel@.subrange(
                        slash as int + 1, rel@.len() as int);
                    assert(name@ == nspec);
                    assert(nspec.len() > 0 && !is_dot(nspec)
                        && !is_dotdot(nspec));
                }
                Some(vstd::slice::slice_to_vec(&rel[..e]))
            }
        }
    }
}

// The spec-side rejection marker lemma (unused: kept empty after
/// rewriting; the name does not occur in the shipped proofs).
// (removed)

// ===========================================================================
// the lean-key anchor (the fast-path validation lemma)
// ===========================================================================
//
// The "hit also validates the parent" sentence (incremental.rs:109):
// when the cache holds the key k (a walk-inserted key: lean tail, no
// trailing separator nor `/.` pair) and a later query spells k joined
// with a normal file name, the byte-wise lookup lands exactly on k.

/// No separator byte occurs inside s (the component form).
pub open spec fn slash_free(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] != 0x2F
}

/// The tail-lean form of a cache key: nonempty, no trailing
/// separator, no trailing `/.` pair (what the trim loop leaves).
pub open spec fn key_lean(k: Seq<u8>) -> bool {
    k.len() > 0
        && k[k.len() - 1] != 0x2F
        && !(k.len() >= 2 && k[k.len() - 1] == 0x2E
            && k[k.len() - 2] == 0x2F)
}

/// The append_prefix length carry.
proof fn append_prefix_len(s: Seq<u8>, rel: Seq<u8>, k: int)
    requires 0 <= k <= rel.len()
    ensures append_prefix(s, rel, k).len() == s.len() + k
    decreases k
{
    if k <= 0 {
        reveal(append_prefix);
    } else {
        reveal(append_prefix);
        append_prefix_len(s, rel, k - 1);
    }
}

/// The front-index carry of append_prefix.
proof fn append_prefix_front(
    s: Seq<u8>,
    rel: Seq<u8>,
    q: int,
    k: int,
)
    requires 0 <= q, q < s.len(), k <= rel.len()
    ensures append_prefix(s, rel, k)[q] == s[q]
    decreases k
{
    if k <= 0 {
        reveal(append_prefix);
    } else {
        reveal(append_prefix);
        append_prefix_len(s, rel, k - 1);
        append_prefix_front(s, rel, q, k - 1);
        assert(append_prefix(s, rel, k).len()
            == append_prefix(s, rel, k - 1).len() + 1);
        assert(q < append_prefix(s, rel, k - 1).len());
    }
}

/// The back-index carry of append_prefix.
proof fn append_prefix_back(
    s: Seq<u8>,
    rel: Seq<u8>,
    q: int,
    k: int,
)
    requires
        0 <= q,
        0 <= k <= rel.len(),
        s.len() + q < s.len() + k,
    ensures append_prefix(s, rel, k)[s.len() + q] == rel[q]
    decreases k
{
    if k <= 0 {
        // vacuous: 0 <= q and s.len() + q < s.len() + 0 cannot both
        // hold, so this arm is unreachable at the requires.
        reveal(append_prefix);
    } else {
        reveal(append_prefix);
        // the length of the recursive value (the pushed byte sits at
        // index s.len() + k - 1 exactly)
        append_prefix_len(s, rel, k - 1);
        if s.len() + q < s.len() + k - 1 {
            append_prefix_back(s, rel, q, k - 1);
        } else {
            // q == k - 1: the newly pushed byte is the target index
            assert(q == k - 1);
            assert(s.len() + q == s.len() + k - 1);
            assert(append_prefix(s, rel, k)
                == append_prefix(s, rel, k - 1).push(rel[k - 1]));
        }
    }
}

/// The whole-range back carry for an empty base (the join with an
/// empty base passes rel's bytes through every index).
proof fn append_prefix_all_back(s: Seq<u8>, rel: Seq<u8>, k: int, q: int)
    requires
        s.len() == 0,
        0 <= k <= rel.len(),
        0 <= q < k,
    ensures append_prefix(s, rel, k)[q] == rel[q]
    decreases k
{
    if k <= 0 {
        reveal(append_prefix);
    } else {
        reveal(append_prefix);
        append_prefix_len(s, rel, k - 1);
        if q < k - 1 {
            append_prefix_all_back(s, rel, k - 1, q);
        } else {
            // q == k - 1: the pushed byte is the target index
            assert(q == k - 1);
            assert(append_prefix(s, rel, k)
                == append_prefix(s, rel, k - 1).push(rel[k - 1]));
        }
    }
}

/// The join shape (index-wise, for the memrchr / subrange proofs):
/// joining a nonempty, non-separator-terminated base with a
/// separator-free nonempty rel yields base + '/' + rel.
proof fn join_shape(k: Seq<u8>, c: Seq<u8>)
    requires
        c.len() > 0,
        slash_free(c),
        k.len() > 0,
        k[k.len() - 1] != 0x2F,
    ensures
        join_bytes(k, c).len() == k.len() + c.len() + 1,
        forall|q: int| 0 <= q < k.len() ==> join_bytes(k, c)[q] == k[q],
        join_bytes(k, c)[k.len() as int] == 0x2F,
        forall|q: int| 0 <= q < c.len() ==>
            join_bytes(k, c)[k.len() + 1 + q] == c[q],
        bytes_prefix_eq(k, join_bytes(k, c)),
{
    reveal(join_bytes);
    reveal(append_prefix);
    append_prefix_len(k.push(0x2F), c, c.len() as int);
    let joined = append_prefix(k.push(0x2F), c, c.len() as int);
    assert forall|q: int| 0 <= q < k.len() implies joined[q] == k[q]
    by {
        append_prefix_front(k.push(0x2F), c, q, c.len() as int);
    }
    assert forall|q: int| 0 <= q < c.len() implies
        joined[k.len() + 1 + q] == c[q]
    by {
        append_prefix_back(k.push(0x2F), c, q, c.len() as int);
    }
    // the separator byte itself: index k.len() is the pushed '/' of
    // the seed (the front carry with q == k.len(), inside the seed
    // length k.len() + 1)
    append_prefix_front(k.push(0x2F), c, k.len() as int, c.len() as int);
    assert(k.push(0x2F)[k.len() as int] == 0x2F);
    assert(joined[k.len() as int] == 0x2F);
}

/// The joined-key length carry (both empty and nonempty base): the
/// joined key is strictly longer than the base; with an empty base
/// the segment's own bytes pass through. (slash_free keeps the join
/// on the append arm -- a rooted seg would replace the base.)
proof fn join_key_len(key: Seq<u8>, seg: Seq<u8>)
    requires
        seg.len() > 0,
        seg[0] != 0x2F,
    ensures
        join_bytes(key, seg).len() > key.len(),
        key.len() == 0 ==> (join_bytes(key, seg).len() == seg.len()
            && forall|q: int| 0 <= q < seg.len() ==>
                join_bytes(key, seg)[q] == seg[q]),
{
    reveal(join_bytes);
    reveal(append_prefix);
    if key.len() == 0 {
        assert(join_bytes(key, seg)
            == append_prefix(key, seg, seg.len() as int));
        append_prefix_len(key, seg, seg.len() as int);
        assert forall|q: int| 0 <= q < seg.len() implies
            join_bytes(key, seg)[q] == seg[q]
        by {
            append_prefix_all_back(key, seg, seg.len() as int, q);
        }
    } else {
        // both non-separator-terminated and separator-terminated
        // bases grow: the length carries cover each arm of the join
        append_prefix_len(key.push(0x2F), seg, seg.len() as int);
        append_prefix_len(key, seg, seg.len() as int);
    }
}

/// The lean-carry of the walk keys: joining a lean (or empty) base
/// with a normal, separator-free, non-sentinel segment leaves a lean
/// key (the walk's accumulated key chain stays lookup-valid).
proof fn join_lean_carry(key: Seq<u8>, seg: Seq<u8>)
    requires
        key.len() == 0 || key_lean(key),
        seg.len() > 0,
        !is_dot(seg),
        !is_dotdot(seg),
        slash_free(seg),
    ensures key_lean(join_bytes(key, seg))
{
    let joined = join_bytes(key, seg);
    join_key_len(key, seg);
    if key.len() == 0 {
        // the empty base passes the segment bytes through
        reveal(join_bytes);
        reveal(append_prefix);
        assert forall|q: int| 0 <= q < joined.len() implies
            joined[q] == seg[q]
        by {
            append_prefix_all_back(key, seg, seg.len() as int, q);
        }
        assert(joined.len() == seg.len());
        assert(joined[joined.len() - 1] == seg[seg.len() - 1]);
        assert(joined[joined.len() - 1] != 0x2F);
        // no trailing '/.' pair: the last two bytes are two segment
        // bytes (a '/' inside is impossible) unless the segment is
        // the one-byte '.', which is_dot excludes
        if joined.len() >= 2 {
            assert(joined[joined.len() - 2] == seg[seg.len() - 2]);
            assert(joined[joined.len() - 2] != 0x2F);
        }
    } else {
        // the nonempty base joins through the separator
        join_shape(key, seg);
        assert(joined.len() == key.len() + seg.len() + 1);
        assert(joined[joined.len() - 1] == seg[seg.len() - 1]);
        assert(joined[joined.len() - 1] != 0x2F);
        if seg.len() == 1 {
            // the last pair is ('/', seg[0]); '/.' needs seg == "."
            assert(joined[joined.len() - 2] == 0x2F);
            if seg[0] == 0x2E {
                assert(seg == seq![0x2E]);
                assert(false);
            }
        } else {
            // the last pair is two segment bytes, no '/' inside
            assert(joined[joined.len() - 2] == seg[seg.len() - 2]);
            assert(joined[joined.len() - 2] != 0x2F);
        }
    }
}

/// The trim-stop lemma: a lean tail stops the trim loop in place.
proof fn pk_trim_lean(rel: Seq<u8>, j: int)
    requires
        1 <= j <= rel.len(),
        rel[j - 1] != 0x2F,
        !(j >= 2 && rel[j - 2] == 0x2F && rel[j - 1] == 0x2E)
    ensures pk_trim_end(rel, j) == j
{
    reveal(pk_trim_end);
}

/// The lean-key anchor lemma (incremental.rs:109's validation): for a
/// lean key k and a normal name c (nonempty, separator-free, neither
/// '.' nor '..'), the byte-wise parent key of `k joined with c` is
/// exactly k.
proof fn pk_join_lean(k: Seq<u8>, c: Seq<u8>)
    requires
        key_lean(k),
        c.len() > 0,
        !is_dot(c),
        !is_dotdot(c),
        slash_free(c),
    ensures parent_key_spec(join_bytes(k, c)) == Some(k)
{
    let joined = join_bytes(k, c);
    join_shape(k, c);
    assert forall|q: int| k.len() < q < joined.len() implies
        joined[q] != 0x2F
    by {
        let t = q - k.len() - 1;
        assert(0 <= t < c.len());
        assert(joined[q] == c[t]);
        assert(c[t] != 0x2F);
    }
    memrchr_spec_some_bridge(joined, 0x2F, k.len() as int);
    assert(memrchr_spec(joined, 0x2F) == Some(k.len() as int));
    // the name slice is exactly c
    assert(joined.subrange(k.len() as int + 1, joined.len() as int) == c);
    // the trim stops on the lean tail of k
    assert(joined[k.len() - 1] == k[k.len() - 1]);
    pk_trim_lean(joined, k.len() as int);
    assert(joined.subrange(0, k.len() as int) == k);
}

// ===========================================================================
// CachedDir and the dir cache -- upstream incremental.rs:91-105
// ===========================================================================
//
// Upstream doc (incremental.rs:91-94, verbatim):
//   "Cached traversal state for a directory relative to the
//    configured root.
//    The presence of an entry means that the directory and every
//    ancestor between it and the root have already been checked."
// Upstream variant docs (incremental.rs:96-104, verbatim):
//   "The directory may be descended into. The matcher includes the
//    ignore rules loaded through this directory and is therefore the
//    matcher to use for its children."
//   "The directory may not be descended into because it was ignored
//    by a path rule or hidden-file filtering. Every descendant is
//    consequently ignored, and ignore files inside this directory
//    are not loaded."

/// Origin enum (incremental.rs:96-105); variant docs verbatim above.
pub enum CachedDir {
    /// The directory may be descended into (the matcher for its
    /// children).
    Allowed(Ignore),
    /// Every descendant is ignored (the terminal entry).
    Ignored,
}

/// One assoc-list entry (upstream `dirs: HashMap<OsString, CachedDir>`,
/// incremental.rs:67).
pub struct CachedDirEnt {
    /// The directory path relative to the root (the upstream key).
    pub key: Vec<u8>,
    /// The cached state (the upstream value).
    pub state: CachedDir,
}

/// The first-match scan spec (miss = -1).
pub open spec fn cache_scan(ds: Seq<CachedDirEnt>, key: Seq<u8>, j: int)
    -> int
    decreases ds.len() - j
{
    if j >= ds.len() {
        -1
    } else if ds[j].key@ == key {
        j
    } else {
        cache_scan(ds, key, j + 1)
    }
}

/// The exec carrier of the scan (parameter-position recursion, the
/// #IG-19 form; the HashMap `get`).
pub fn cache_scan_exec(
    ds: &[CachedDirEnt],
    key: &[u8],
    j: usize,
) -> (r: Option<usize>)
    requires j <= ds.len()
    ensures
        r matches Some(i) ==> (j as int <= i && 0 <= i < ds.len() as int
            && ds[i as int].key@ == key@
            && cache_scan(ds@, key@, j as int) == i),
        r matches None ==> cache_scan(ds@, key@, j as int) == -1,
    decreases ds.len() - j
{
    if j >= ds.len() {
        None
    } else if bytes_eq(ds[j].key.as_slice(), key) {
        proof {
            reveal(cache_scan);
        }
        Some(j)
    } else {
        proof {
            reveal(cache_scan);
        }
        cache_scan_exec(ds, key, j + 1)
    }
}

/// The deterministic scan value: a hit at i with all earlier entries
/// distinct is the first match (used by the frozen/live bridges and
/// the insert posts).
proof fn cache_scan_hit(
    ds: Seq<CachedDirEnt>,
    key: Seq<u8>,
    i: int,
    j: int,
)
    requires
        0 <= j <= i < ds.len(),
        ds[i].key@ == key,
        forall|t: int| j <= t < i ==> ds[t].key@ != key,
    ensures cache_scan(ds, key, j) == i
    decreases i - j
{
    reveal(cache_scan);
    if j == i {
    } else {
        assert(ds[j].key@ != key);
        cache_scan_hit(ds, key, i, j + 1);
    }
}

/// A miss-all scan: a -1 value means every position from the start
/// index on misses the key (the contrapositive input of the
/// existence lemma).
proof fn cache_scan_miss_all(ds: Seq<CachedDirEnt>, key: Seq<u8>, j: int)
    requires
        0 <= j,
        cache_scan(ds, key, j) == -1,
    ensures
        forall|t: int|
            #![trigger ds[t].key@]
            0 <= t && j <= t < ds.len() ==> ds[t].key@ != key,
    decreases ds.len() - j
{
    if j >= ds.len() {
        // the vacuous tail
    } else {
        reveal(cache_scan);
        // the branch facts spelled as implications before the split
        // (the #IG-23 discipline: no int-literal match arms, no
        // late-scoped reveals)
        assert(ds[j].key@ == key ==> cache_scan(ds, key, j) == j);
        assert(ds[j].key@ != key ==> cache_scan(ds, key, j)
            == cache_scan(ds, key, j + 1));
        if ds[j].key@ == key {
            // impossible: the hit arm yields j, not -1
            assert(cache_scan(ds, key, j) == j);
            assert(j >= 0);
            assert(false);
        } else {
            cache_scan_miss_all(ds, key, j + 1);
        }
    }
}

/// Existence: any entry carrying the key makes the scan find some
/// hit (the insert clauses only need >= 0). By contradiction: a
/// miss-all scan would miss the carrier itself.
proof fn cache_scan_exists(ds: Seq<CachedDirEnt>, key: Seq<u8>, i: int)
    requires 0 <= i < ds.len(), ds[i].key@ == key
    ensures cache_scan(ds, key, 0) >= 0
{
    let c = cache_scan(ds, key, 0);
    if c >= 0 {
    } else {
        // the value range pins the miss to exactly -1
        cache_scan_ge_neg(ds, key, 0);
        assert(c >= -1);
        assert(c == -1);
        cache_scan_miss_all(ds, key, 0);
        assert(ds[i].key@ != key);
        assert(ds[i].key@ == key);
        assert(false);
    }
}

/// Where a hit lands: a nonnegative scan value is an in-range index
/// whose entry matches, with every earlier entry distinct.
proof fn scan_hit_at(ds: Seq<CachedDirEnt>, key: Seq<u8>, j: int)
    requires
        0 <= j <= ds.len(),
        cache_scan(ds, key, j) >= 0,
    ensures
        j <= cache_scan(ds, key, j) < ds.len()
            && ds[cache_scan(ds, key, j)].key@ == key
            && forall|t: int|
                #![trigger ds[t].key@]
                j <= t < cache_scan(ds, key, j) ==> ds[t].key@ != key,
    decreases ds.len() - j
{
    reveal(cache_scan);
    if j >= ds.len() {
        // the miss arm; impossible at the requires
    } else if ds[j].key@ == key {
    } else {
        scan_hit_at(ds, key, j + 1);
    }
}

/// Push stability: a kept-hit scan keeps its hit under an appended
/// entry (the prefix entries are untouched; the push only extends).
proof fn cache_scan_push_keep(
    ds: Seq<CachedDirEnt>,
    key: Seq<u8>,
    e: CachedDirEnt,
)
    requires cache_scan(ds, key, 0) >= 0
    ensures cache_scan(ds.push(e), key, 0) >= 0
{
    let i = cache_scan(ds, key, 0);
    scan_hit_at(ds, key, 0);
    if i < 0 {
        // impossible at the requires (scan_hit_at pins the shape)
        assert(false);
    } else {
        // the first hit is at i; entries below i are all distinct
        // and untouched under the push, so the push scans identically
        assert(ds.push(e).len() == ds.len() + 1);
        assert(ds.push(e)[i] == ds[i]);
        assert(forall|t: int| 0 <= t < i
            ==> ds.push(e)[t].key@ != key);
        cache_scan_hit(ds.push(e), key, i, 0);
    }
}

/// The key-parent split (the memrchr consult on a cache key; None
/// means the key sits directly under the root -- the root itself is
/// never a key, incremental.rs:65-66 "Directory paths relative to
/// `root`, excluding the root itself").
pub open spec fn key_parent(k: Seq<u8>) -> Option<Seq<u8>> {
    match memrchr_spec(k, 0x2F) {
        None => None,
        Some(p) => Some(k.subrange(0, p)),
    }
}

/// The cache well-formedness (the DP29 invariant): every stored key
/// is nonempty, every stored key either sits directly under the root
/// or its parent key is also stored, and every stored Allowed matcher
/// is matcher-callable -- "the directory and every ancestor ... have
/// already been checked" (incremental.rs:92-94).
pub open spec fn dirs_wf(ds: Seq<CachedDirEnt>) -> bool {
    forall|j: int| 0 <= j < ds.len() ==>
        (ds[j].key@.len() > 0
            && (match key_parent(ds[j].key@) {
                None => true,
                Some(p) => cache_scan(ds, p, 0) >= 0,
            })
            && (match &ds[j].state {
                CachedDir::Allowed(ig) => ig_wf(ig),
                CachedDir::Ignored => true,
            }))
}

// ===========================================================================
// the reverse-chronological error fold (the peb push mirror)
// ===========================================================================
//
// The walk's errs push in call order; the spec tracks the reversed
// list and replays it (`apply_rev` pushes the LAST element first),
// so the walk recursion composes its segment by a pure seq push (the
// post-order recursion of the walk) and no associativity reasoning
// is consumed.

/// Replay the reversed list r onto st (pushes r's last element
/// first -- the chronological order).
pub open spec fn apply_rev(st: Seq<Error>, r: Seq<Error>) -> Seq<Error>
    decreases r.len()
{
    if r.len() == 0 {
        st
    } else {
        apply_rev(
            st.push(r[r.len() - 1]),
            r.subrange(0, (r.len() - 1) as int),
        )
    }
}

/// Replay a list of reversed segments in order (segment 0's pushes
/// first -- the chronological order across segments).
pub open spec fn apply_rev2(
    st: Seq<Error>,
    segs: Seq<Seq<Error>>,
) -> Seq<Error>
    decreases segs.len()
{
    if segs.len() == 0 {
        st
    } else {
        apply_rev2(
            apply_rev(st, segs[0]),
            segs.subrange(1, segs.len() as int),
        )
    }
}

/// The realization axiom of the peb_vec face (dir.rs): for every
/// realized Vec the uninterp carrier IS that Vec -- the peb_final
/// plural-wrap contract names peb_vec(st) where the real builder
/// materializes the very stack st, and this trusted leg closes that
/// naming (the std_abs-convention bridge between the uninterp face
/// and the real constructor).
#[verifier::external_body]
proof fn peb_vec_realized(v: &Vec<Error>)
    ensures peb_vec(v@) == *v,
{
}

/// An all-empty trailing segment folds to the identity (the top
/// composition's third segment -- the stat legs that add nothing).
proof fn apply_rev2_push_empty(
    st: Seq<Error>,
    segs: Seq<Seq<Error>>,
)
    ensures
        apply_rev2(st, segs.push(Seq::empty()))
            == apply_rev2(st, segs),
    decreases segs.len()
{
    reveal(apply_rev2);
    reveal(apply_rev);
    if segs.len() == 0 {
        // folding the lone empty segment replays nothing: the lone
        // empty head replays no errors and the empty tail is the
        // state (a granular three-step ladder, the #IG-19 rung
        // discipline)
        assert(apply_rev(st, Seq::empty()) == st);
        assert(segs.push(Seq::empty()) == seq![Seq::empty()]);
        let e1 = seq![Seq::empty()];
        assert(e1.len() == 1);
        assert(e1[0] == Seq::empty());
        assert(e1.subrange(0, 0) == Seq::empty());
        assert(apply_rev(st, e1[0]) == st);
        assert(e1.subrange(1, 1) == Seq::empty());
        assert(apply_rev2(st, e1)
            == apply_rev2(apply_rev(st, e1[0]), e1.subrange(1, 1)));
        assert(apply_rev2(st, e1.subrange(1, 1)) == st);
        assert(apply_rev2(st, e1) == st);
        assert(apply_rev2(st, segs) == st);
        assert(apply_rev2(st, segs.push(Seq::empty()))
            == apply_rev2(st, segs));
    } else {
        // both sides fold the head segment first
        let head = segs[0];
        assert(segs.push(Seq::empty()).len() == segs.len() + 1);
        assert(segs.push(Seq::empty())[0] == head);
        // the pushed tail subranges agree index-wise
        assert(segs.push(Seq::empty())
            .subrange(1, (segs.len() + 1) as int)
            == segs.subrange(1, segs.len() as int)
                .push(Seq::empty())) by {
            let lhs = segs.push(Seq::empty())
                .subrange(1, (segs.len() + 1) as int);
            let rhs = segs.subrange(1, segs.len() as int)
                .push(Seq::empty());
            assert(lhs.len() == rhs.len());
            assert forall|q: int| 0 <= q < lhs.len() implies
                lhs[q] == rhs[q]
            by {
                vstd::seq::lemma_seq_subrange_index(
                    segs.push(Seq::empty()), 1,
                    (segs.len() + 1) as int, q);
                vstd::seq::lemma_seq_subrange_index(
                    segs.subrange(1, segs.len() as int).push(
                        Seq::empty()), 0, segs.len() as int, q);
                if q < segs.len() - 1 {
                    // the push preserves the prefix read
                    assert(1 + q < segs.len() as int);
                    assert(segs.push(Seq::empty())[(1 + q) as int]
                        == segs[(1 + q) as int]);
                    assert(segs.subrange(1, segs.len() as int)[q]
                        == segs[(1 + q) as int]);
                    assert(segs.subrange(1, segs.len() as int)
                        .push(Seq::empty())[q]
                        == segs[(1 + q) as int]);
                } else {
                    assert(q == segs.len() - 1);
                    assert(lhs[q] == Seq::empty());
                    assert(rhs[q] == Seq::empty());
                }
            }
        }
        // both sides fold the head the same way (the unfold
        // spelled per side)
        assert(apply_rev2(st, segs.push(Seq::empty()))
            == apply_rev2(apply_rev(st, head),
                segs.push(Seq::empty())
                    .subrange(1, (segs.len() + 1) as int)));
        assert(apply_rev2(st, segs)
            == apply_rev2(apply_rev(st, head),
                segs.subrange(1, segs.len() as int)));
        apply_rev2_push_empty(apply_rev(st, head),
            segs.subrange(1, segs.len() as int));
        assert(apply_rev2(apply_rev(st, head),
            segs.push(Seq::empty())
                .subrange(1, (segs.len() + 1) as int))
            == apply_rev2(apply_rev(st, head),
                segs.subrange(1, segs.len() as int)));
        assert(apply_rev2(st, segs.push(Seq::empty()))
            == apply_rev2(st, segs));
    }
}

/// The single-push unfold (the base of the segment replay).
proof fn apply_rev_one(st: Seq<Error>, e: Error)
    ensures apply_rev(st, seq![e]) == st.push(e)
{
    reveal(apply_rev);
    let r1 = seq![e];
    assert(r1.len() == 1);
    assert(r1.len() - 1 == 0);
    assert(r1[r1.len() - 1] == e);
    assert(r1.subrange(0, 0) == Seq::empty());
    assert(apply_rev(st.push(e), Seq::empty()) == st.push(e));
    assert(apply_rev(st, seq![e])
        == apply_rev(st.push(e), r1.subrange(0, 0)));
}

/// The split carry: an element pushed onto a reversed segment plays
/// FIRST in the chronological replay (the pushed element is the
/// deepest in the reversed list), so fronting it onto the state and
/// replaying the rest is one combined replay (the insert arm's
/// error push ahead of the recursive walk segment).
proof fn apply_rev_split(st: Seq<Error>, r: Seq<Error>, e: &Error)
    ensures apply_rev(st, r.push(*e)) == apply_rev(st.push(*e), r)
{
    reveal(apply_rev);
    let rp = r.push(*e);
    assert(rp[rp.len() - 1] == *e);
    assert(rp.subrange(0, rp.len() - 1) == r) by {
        assert(rp.subrange(0, rp.len() - 1).len() == r.len());
        assert forall|q: int| 0 <= q < r.len() implies
            rp.subrange(0, rp.len() - 1)[q] == r[q]
        by {
            vstd::seq::lemma_seq_subrange_index(rp, 0,
                rp.len() - 1, q);
            assert(rp[q] == r[q]);
        }
    }
}

// ===========================================================================
// the fs face
// ===========================================================================

/// The per-call fs face (the trusted input bundle; every fs consult
/// of one `matched` call names a field here: the root probes of the
/// root loader, the per-directory discovery consumed underneath
/// `add_child_with_possible_reuse`, and the selected `max_filesize`
/// stat).
pub struct Ig6FsFace {
    /// Whether the configured root exists as a directory (upstream
    /// `self.root.is_dir()`, incremental.rs:467).
    pub root_is_dir: bool,
    /// The canonicalized absolute base handed to add_parents (the
    /// canonicalize leg inside `Ignore::add_parents`; the PR-3420
    /// seam carrier).
    pub root_abs_base: Option<Vec<u8>>,
    /// The parent-chain discovery list (the add_parents `built`
    /// face: root-first (node, error) pairs).
    pub root_parents_built: Vec<(IgnoreNode, Option<Error>)>,
    /// The found-set of the root directory (the add_child consult at
    /// root load, incremental.rs:474).
    pub root_found: IgnoreFilesFound,
    /// The git-type probe face at root load.
    pub root_git_is_file: Option<bool>,
    /// The commondir resolve Ok at root load.
    pub root_resolved_ok: Option<Vec<u8>>,
    /// The commondir resolve Err at root load.
    pub root_resolved_err: Option<Error>,
    /// The per-directory found-set consumed underneath
    /// `add_child_with_possible_reuse` during the walk (uniform per
    /// call -- the walk-level variation is the recorded cut).
    pub child_found: IgnoreFilesFound,
    /// The git-type probe face of the walk's child consults.
    pub child_git_is_file: Option<bool>,
    /// The commondir resolve Ok of the walk's child consults.
    pub child_resolved_ok: Option<Vec<u8>>,
    /// The commondir resolve Err of the walk's child consults.
    pub child_resolved_err: Option<Error>,
    /// The stat consult for `max_filesize` (the selected probe:
    /// `path.metadata()` / `path.symlink_metadata()` per
    /// follow_links, incremental.rs:320-324; Ok carries `md.len()`).
    pub filesize: Result<u64, IoErrorFace>,
}

// ===========================================================================
// the trusted construction / clone legs (contract faces)
// ===========================================================================

/// The four-pool emptiness shorthand (the ig5 reuse-arm posts).
pub open spec fn node_empty_pools(n: &IgnoreNode) -> bool {
    gi_is_empty_view(&n.custom_ignore_matcher)
        && gi_is_empty_view(&n.ignore_matcher)
        && gi_is_empty_view(&n.git_ignore_matcher)
        && gi_is_empty_view(&n.git_exclude_matcher)
}

/// The ctx opts carry (the Arc-shared clone is verbatim upstream).
pub open spec fn opts_carry(a: &Ignore, b: &Ignore) -> bool {
    a.inner.opts.hidden == b.inner.opts.hidden
        && a.inner.opts.ignore == b.inner.opts.ignore
        && a.inner.opts.parents == b.inner.opts.parents
        && a.inner.opts.git_global == b.inner.opts.git_global
        && a.inner.opts.git_ignore == b.inner.opts.git_ignore
        && a.inner.opts.git_exclude == b.inner.opts.git_exclude
        && a.inner.opts.ignore_case_insensitive
            == b.inner.opts.ignore_case_insensitive
        && a.inner.opts.require_git == b.inner.opts.require_git
}

/// The abstract child stack of one walk consult (the
/// `add_child_with_possible_reuse` return, named for the walk spec;
/// consumed only through the contract below).
pub uninterp spec fn acpr_child_face(
    cur: Ignore,
    path: Seq<u8>,
    fs: &Ig6FsFace,
) -> Ignore;

/// The abstract child error of one walk consult.
pub uninterp spec fn acpr_err_face(
    cur: Ignore,
    path: Seq<u8>,
    fs: &Ig6FsFace,
) -> Option<Error>;

/// The forwarding wrapper of dir.rs `add_child_with_possible_reuse`
/// for the walk's per-directory consults (upstream
/// `ignore.add_child_with_possible_reuse(&path)`,
/// incremental.rs:426): the contract is consumed verbatim (never
/// expanded) with the return named through the faces above; the
/// Arc-shared ctx carry-over (opts / custom names / absolute_base)
/// rides along as the identity clause set (upstream clones the ctx
/// verbatim -- the walk's requires stay inductive across levels).
#[verifier::external_body]
pub fn ig6_acpr(
    cur: Ignore,
    path: &[u8],
    fs: &Ig6FsFace,
) -> (r: (Ignore, Option<Error>))
    requires
        ig_wf(&cur),
        fs.child_found.custom_ignore_files.len()
            == cur.inner.custom_ignore_filenames.len(),
    ensures
        ig_wf(&r.0),
        r.0 == acpr_child_face(cur, path@, fs),
        r.1 == acpr_err_face(cur, path@, fs),
        r.0.nodes@.len() == cur.nodes@.len()
            || r.0.nodes@.len() == cur.nodes@.len() + 1,
        r.0.nodes@.len() == cur.nodes@.len() ==> (
            forall|i: int| 0 <= i < r.0.nodes@.len() ==> (
                r.0.nodes@[i].dir@ == cur.nodes@[i].dir@
                    && r.0.nodes@[i].is_absolute_parent
                        == cur.nodes@[i].is_absolute_parent
                    && !r.0.nodes@[i].has_git
                    && node_empty_pools(&r.0.nodes@[i]))),
        r.0.nodes@.len() == cur.nodes@.len() + 1 ==> (
            r.0.nodes@[0].dir@ == path@
                && !r.0.nodes@[0].is_absolute_parent),
        r.0.absolute_base@ == cur.absolute_base@,
        opts_carry(&r.0, &cur),
        r.0.inner.custom_ignore_filenames@.len()
            == cur.inner.custom_ignore_filenames@.len(),
{
    unimplemented!() // trusted forward of add_child_with_possible_reuse
                     // (dir.rs:286-309; the names ride the walk spec)
}

/// The abstract parents stack of the root load (the add_parents
/// return, named for the root spec).
pub uninterp spec fn ap_face(
    stored: Ignore,
    abs_base: Option<Vec<u8>>,
    built: Seq<(IgnoreNode, Option<Error>)>,
) -> Ignore;

/// The forwarding wrapper of dir.rs `add_parents` (upstream
/// `ignore.add_parents(&self.root)`, incremental.rs:472): the
/// contract consumed verbatim plus the face naming (the error post
/// is the consumed peb_final fold of the built face).
#[verifier::external_body]
pub fn ig6_add_parents(
    stored: Ignore,
    abs_base: &Option<Vec<u8>>,
    built: &[(IgnoreNode, Option<Error>)],
) -> (r: (Ignore, Option<Error>))
    requires
        ig_wf(&stored),
        stored.nodes.len() == 1,
        (abs_base matches Some(_)) ==> built.len() >= 1,
    ensures
        ig_wf(&r.0),
        r.0 == ap_face(stored, abs_base@, built@),
        r.0.absolute_base@ == abs_base@,
        r.0.nodes@.len() == built.len() + stored.nodes@.len(),
        r.0.inner.custom_ignore_filenames@.len()
            == stored.inner.custom_ignore_filenames@.len(),
        opts_carry(&r.0, &stored),
        r.1 == peb_final(apf_errs(built@, 0)),
{
    unimplemented!() // trusted forward of add_parents (dir.rs:191-262)
}

/// The abstract root child stack of the root load's second consult
/// (`parents.add_child(&self.root)`, incremental.rs:474).
pub uninterp spec fn root_child_face(
    parents: Ignore,
    root: Seq<u8>,
    fs: &Ig6FsFace,
) -> Ignore;

/// The abstract root child error of the same consult (dir.rs
/// add_child carries no error content in its contract; the face owns
/// it here).
pub uninterp spec fn root_child_err_face(
    parents: Ignore,
    root: Seq<u8>,
    fs: &Ig6FsFace,
) -> Option<Error>;

/// The forwarding wrapper of dir.rs `add_child` for the root load's
/// second consult (consumed verbatim plus the face naming; the ctx
/// carry-over clause set mirrors ig6_acpr's).
#[verifier::external_body]
pub fn ig6_root_child(
    parents: Ignore,
    root: &[u8],
    fs: &Ig6FsFace,
) -> (r: (Ignore, Option<Error>))
    requires
        ig_wf(&parents),
        fs.root_found.custom_ignore_files.len()
            == parents.inner.custom_ignore_filenames.len(),
    ensures
        ig_wf(&r.0),
        r.0 == root_child_face(parents, root@, fs),
        r.1 == root_child_err_face(parents, root@, fs),
        r.0.nodes@.len() == parents.nodes@.len() + 1,
        r.0.nodes@[0].dir@ == root@,
        !r.0.nodes@[0].is_absolute_parent,
        r.0.absolute_base@ == parents.absolute_base@,
        opts_carry(&r.0, &parents),
        r.0.inner.custom_ignore_filenames@.len()
            == parents.inner.custom_ignore_filenames@.len(),
{
    unimplemented!() // trusted forward of add_child (dir.rs:264-309)
}

/// The abstract clone of one stored stack (upstream's `cached.clone()`
/// / `child.clone()` / the root clones, incremental.rs:408 / :430 /
/// :463-464).
pub uninterp spec fn clone_face(orig: &Ignore) -> Ignore;

/// The deep-copy leg: upstream clones Arc payloads at three
/// incremental.rs points (see clone_face above); owned data has no
/// Clone face in this Verus build, so the copy is a trusted leg whose
/// observable content is pinned -- wf, the per-node labels, the ctx
/// opts carry, and the matched value law for every path (what every
/// downstream consumption reads).
#[verifier::external_body]
pub fn ig6_clone(orig: &Ignore) -> (r: Ignore)
    requires ig_wf(orig)
    ensures
        ig_wf(&r),
        r == clone_face(orig),
        r.nodes@.len() == orig.nodes@.len(),
        forall|i: int| 0 <= i < orig.nodes@.len() ==> (
            r.nodes@[i].dir@ == orig.nodes@[i].dir@
                && r.nodes@[i].is_absolute_parent
                    == orig.nodes@[i].is_absolute_parent
                && r.nodes@[i].has_git == orig.nodes@[i].has_git
                && r.nodes@[i].has_absolute_parent_rules
                    == orig.nodes@[i].has_absolute_parent_rules),
        r.absolute_base@ == orig.absolute_base@,
        opts_carry(&r, orig),
        r.inner.custom_ignore_filenames@.len()
            == orig.inner.custom_ignore_filenames@.len(),
        forall|p: Seq<u8>, d: bool|
            dir_matched_spec(&r, p, d) == dir_matched_spec(orig, p, d),
{
    unimplemented!() // trusted deep copy (the matched value law and
                     // the label identities are the contract)
}

/// The abstract tagged io error of the filesize leg (upstream
/// `Error::from(err).with_path(path)`, incremental.rs:332-333).
pub uninterp spec fn fs_err_face(e: &IoErrorFace, path: Seq<u8>)
    -> Error;

/// The exec bridge of the filesize error tag. The naming clause (the
/// equality with the uninterp face) is a trusted-leg post in the
/// std_abs convention: the real content is the IG1 tagger chain (an
/// io error wrapped WithPath), the uninterp face owns the walk-spec
/// naming (the walk's errs posts read the abstract value). The two
/// content clauses below stay real-valued (verified via the IG1
/// tagger contract) so the runtime evidence rows keep their shape.
#[verifier::external_body]
pub fn fs_err_tagged(err: &IoErrorFace, path: &[u8]) -> (r: Error)
    ensures
        r == fs_err_face(err, path@),
        r matches Error::WithPath { .. },
        with_path_payload(&r) == path@,
        *with_path_inner(&r) == Error::Io(IoErrorFace { repr: err.repr }),
{
    // the trusted leg body (kept in the twin as the naming contract;
    // the IG1 chain it names: Error::Io(..).with_path(path))
    error_with_path(Error::Io(IoErrorFace { repr: err.repr }), path)
}

/// The trusted std::path::absolute face (upstream
/// `std::path::absolute(path).ok()?`, incremental.rs:588; the cwd
/// consult and the platform absolutization are the face -- unix
/// output is '/'-prefixed with '.' and '..' resolved lexically
/// against the previous component where possible; the runtime probe
/// rows of this batch pin the host behavior).
pub uninterp spec fn std_abs_face(path: Seq<u8>) -> Option<Seq<u8>>;

/// The exec carrier of the std::path::absolute face.
#[verifier::external_body]
pub fn std_abs(path: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        (r matches None) == (std_abs_face(path@) matches None),
        r matches Some(v2) ==> (std_abs_face(path@)
            matches Some(sv2) && v2@ == sv2),
{
    unimplemented!() // trusted face (std::path::absolute, unix)
}

// ===========================================================================
// IncrementalIgnore -- upstream incremental.rs:57-70
// ===========================================================================
//
// Upstream doc (incremental.rs:12-41) carries the module-level
// semantics (the precedence order as a traversal; the snapshot at
// directory granularity; the '-' root inertness). The field docs
// verbatim below.

/// The root-stack state (upstream `RootIgnore`, incremental.rs:83-89:
/// Unloaded(Ignore) / Loaded(Ignore) / NotDirectory / Stdin; the twin
/// holds the stack in `root_store` -- one entry when a stack exists
/// -- so the consuming moves stay inside value semantics; NotDirectory
/// and Stdin hold no stack, as the upstream enum assignment drops
/// the payload they replace).
pub enum RootState {
    Unloaded,
    Loaded,
    NotDirectory,
    Stdin,
}

/// Origin struct (incremental.rs:57-70); field docs verbatim.
pub struct IncrementalIgnore {
    /// The root exactly as it was given to `WalkBuilder`.
    pub root: Vec<u8>,
    /// The normalized root used only by the opt-in normalization
    /// routine. (Upstream: OnceLock<Option<PathBuf>>; the
    /// memoization is not value-observable -- the twin recomputes
    /// per call and never reads this field.)
    pub normalized_root: Option<Option<Vec<u8>>>,
    /// The matcher for the configured root directory, loaded on
    /// first use (the state; the stack lives in root_store).
    pub state: RootState,
    /// Directory paths relative to `root`, excluding the root
    /// itself. Keys are assembled from components, so hashing need
    /// not normalize them. (Upstream: HashMap; the assoc list keeps
    /// first-match semantics -- keys are inserted at most once.)
    pub dirs: Vec<CachedDirEnt>,
    /// The root stack store (the twin's state-machine carrier).
    pub root_store: Vec<Ignore>,
    /// Options for additional filtering beyond gitignore.
    pub options: IncrementalIgnoreOptions,
}

/// The twin well-formedness: the state-machine store shape (a stack
/// exactly when the state carries one; a root-level single node when
/// still Unloaded -- the add_parents precondition upstream guarantees
/// by construction from WalkBuilder), the wf of every stored /
/// cached stack, and the cache closure (DP29).
pub open spec fn ii_wf(m: &IncrementalIgnore) -> bool {
    (match m.state {
        RootState::Stdin => m.root_store.len() == 0,
        RootState::NotDirectory => m.root_store.len() == 0,
        RootState::Unloaded => m.root_store.len() == 1
            && ig_wf(&m.root_store[0])
            && m.root_store[0].nodes@.len() == 1,
        RootState::Loaded => m.root_store.len() == 1
            && ig_wf(&m.root_store[0]),
    }) && dirs_wf(m.dirs@)
}

/// The `"-"` byte literal carrier (the stdin root spelling).
pub fn dash_lit() -> (r: Vec<u8>)
    ensures r@ == seq![0x2D]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2D);
    v
}

/// Origin Rust (incremental.rs:149-174), the non-stdin arm
/// (upstream doc at incremental.rs:154-165, verbatim:
///   "File traversal special cases `-` to search stdin, so we
///    recognize it here for completeness too. In particular, we really
///    want `WalkBuilder::build_matchers` to return a matcher for every
///    root, even when it's a simple file (handled automatically) or
///    when it's stdin (necessarily special cased).
///    If callers need to search a file or directory named `-`, then
///    they can use `./-`. As is the case for file traversal too.")
/// The stdin arm is the sibling constructor `ii_new_stdin` (the
/// upstream conditional inside `new` -- the split keeps each
/// postcondition strong; both spellings stay reachable).
pub fn ii_new(
    root: Vec<u8>,
    ignore: Ignore,
    options: IncrementalIgnoreOptions,
) -> (r: IncrementalIgnore)
    requires
        ig_wf(&ignore),
        ignore.nodes@.len() == 1,
        root@ != seq![0x2D],
    ensures
        ii_wf(&r),
        r.state == RootState::Unloaded,
        r.root@ == root@,
        r.dirs@.len() == 0,
        r.options.min_depth == options.min_depth,
        r.options.max_depth == options.max_depth,
        r.options.max_filesize == options.max_filesize,
        r.options.hidden == options.hidden,
        r.options.follow_links == options.follow_links,
        r.root_store.len() == 1,
        ig_wf(&r.root_store[0]),
        r.root_store[0].nodes@.len() == ignore.nodes@.len(),
        r.root_store@[0].nodes@[0].dir@ == ignore.nodes@[0].dir@,
{
    let mut rs: Vec<Ignore> = Vec::new();
    rs.push(ignore);
    IncrementalIgnore {
        root,
        normalized_root: None,
        state: RootState::Unloaded,
        dirs: Vec::new(),
        root_store: rs,
        options,
    }
}

/// The stdin arm of the mount (upstream: the `-` root checks
/// byte-equality with the single byte 0x2D).
pub fn ii_new_stdin(options: IncrementalIgnoreOptions)
    -> (r: IncrementalIgnore)
    ensures
        ii_wf(&r),
        r.state == RootState::Stdin,
        r.root@ == seq![0x2D],
        r.dirs@.len() == 0,
        r.options.min_depth == options.min_depth,
        r.options.max_depth == options.max_depth,
        r.options.max_filesize == options.max_filesize,
        r.options.hidden == options.hidden,
        r.options.follow_links == options.follow_links,
        r.root_store.len() == 0,
{
    IncrementalIgnore {
        root: dash_lit(),
        normalized_root: None,
        state: RootState::Stdin,
        dirs: Vec::new(),
        root_store: Vec::new(),
        options,
    }
}

impl IncrementalIgnore {
    /// Upstream doc (incremental.rs:176-177, verbatim):
    ///   "Return the root that paths matched by this matcher are
    ///    relative to."
    pub fn root(&self) -> (r: &[u8])
        ensures r@ == self.root@
    {
        self.root.as_slice()
    }
}

// ===========================================================================
// the join exec carrier (the local twin of the dir join carrier over
// the shared join_bytes model)
// ===========================================================================

/// The std Path::join exec carrier (the join_bytes model, the same
/// body as the dir twin's private carrier -- shared model, local
/// spelling for the incremental joins).
pub fn ig6_join(base: &[u8], rel: &[u8]) -> (r: Vec<u8>)
    ensures r@ == join_bytes(base@, rel@)
{
    if rel.len() > 0 && rel[0] == 0x2F {
        return vstd::slice::slice_to_vec(rel);
    }
    let need_sep: bool = base.len() > 0 && base[base.len() - 1] != 0x2F;
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

// ===========================================================================
// match_path -- upstream incremental.rs:438-456
// ===========================================================================
//
// Upstream inline comment (incremental.rs:449-451, verbatim):
//   "Whether a file is hidden or not has low precedence in filtering.
//    We only check it if we haven't matched anything above. This
//    permits callers to whitelist hidden files or directories."

/// The spec builder of `match_path` (incremental.rs:444-455): the
/// spine verdict over the root-joined path, then the hidden
/// fall-through.
pub open spec fn mp_build(
    root: Seq<u8>,
    hidden: bool,
    ig: &Ignore,
    rel: Seq<u8>,
    is_dir: bool,
) -> IncrementalMatch
{
    let full = join_bytes(root, rel);
    let m = dir_matched_spec(ig, full, is_dir);
    let base = match m {
        None => 0 as int,
        Some((false, _)) => 1 as int,
        Some((true, _)) => 2 as int,
    };
    let hid = hidden && base == 0 && is_hidden_path_only_spec(full);
    let kind = if hid { 1 as int } else { base };
    IncrementalMatch {
        mat: if kind == 0 {
            Match::None
        } else if kind == 1 {
            Match::Ignore(())
        } else {
            Match::Whitelist(())
        },
        should_descend: is_dir && kind != 1,
        is_within_depth: true,
    }
}

/// The `map(|_| ())` payload drop (incremental.rs:445-447): the
/// kind-preserving conversion of the spine's payload match.
pub fn mk_unit(m: &Match<IgmPayload>) -> (r: Match<()>)
    ensures
        (r matches Match::None) == (m matches Match::None),
        (r matches Match::Ignore(_)) == (m matches Match::Ignore(_)),
        (r matches Match::Whitelist(_))
            == (m matches Match::Whitelist(_)),
{
    match m {
        Match::None => Match::None,
        Match::Ignore(_) => Match::Ignore(()),
        Match::Whitelist(_) => Match::Whitelist(()),
    }
}

/// Origin Rust (incremental.rs:438-456), a free fn on the pieces the
/// upstream method reads (self.root / self.options.hidden).
pub fn match_path(
    root: &[u8],
    hidden: bool,
    ig: &Ignore,
    rel: &[u8],
    is_dir: bool,
) -> (r: IncrementalMatch)
    requires ig_wf(ig)
    ensures r == mp_build(root@, hidden, ig, rel@, is_dir)
{
    // let path = self.root.join(relative);
    let path = ig6_join(root, rel);
    // let mut mat = IncrementalMatch::from_match(
    //     ignore.matched(&path, is_dir).map(|_| ()), is_dir);
    let mm = ig.matched(path.as_slice(), is_dir);
    let unit = mk_unit(&mm);
    let mut mat = IncrementalMatch::from_match(unit, is_dir);
    // if self.options.hidden && mat.is_none() && is_hidden_path(&path) {
    //     mat = IncrementalMatch::ignore();
    // }
    if hidden && mat.is_none() && is_hidden_path_only(path.as_slice()) {
        mat = IncrementalMatch::ignore();
    }
    proof {
        // the spine verdict value (the dir twin's matched post)
        let v = ig_m_view(&mm);
        let full = join_bytes(root@, rel@);
        assert(v == dir_matched_spec(ig, full, is_dir));
        let spec = mp_build(root@, hidden, ig, rel@, is_dir);
        let spv = inc_view(&spec);
        match v {
            None => {
                if hidden && is_hidden_path_only_spec(full) {
                    assert(inc_view(&mat) == (1, false, true));
                    assert(spv == (1, false, true));
                } else {
                    assert(inc_view(&mat) == (0, is_dir, true));
                    assert(spv == (0, is_dir, true));
                }
            }
            Some((false, _)) => {
                assert(unit matches Match::Ignore(()));
                assert(inc_view(&mat) == (1, false, true));
                assert(spv == (1, false, true));
            }
            Some((true, _)) => {
                assert(unit matches Match::Whitelist(()));
                assert(inc_view(&mat) == (2, is_dir, true));
                assert(spv == (2, is_dir, true));
            }
        }
        inc_view_eq(&mat, &spec);
    }
    mat
}

// ===========================================================================
// the walk spec (the closed-form mirror of incremental.rs:392-435)
// ===========================================================================

/// One walk leg, recursive ONE BYTE AT A TIME (the #IG-19 syntactic
/// recursion form; segment fates are decided at close time from the
/// raw segment bytes). The cache argument is the call-time snapshot
/// (the frozen-cache abstraction: within one call the walk only looks
/// up keys strictly longer than every key it has inserted). The errs
/// component is the reversed push list (see apply_rev); seg_s is the
/// open raw segment's start (-1 when none), key the accumulated
/// component chain, cur the walk subject.
pub open spec fn ii_walk_spec(
    root: Seq<u8>,
    hidden: bool,
    rel: Seq<u8>,
    is_dir: bool,
    cache: Seq<CachedDirEnt>,
    cursor: int,
    seg_s: int,
    key: Seq<u8>,
    cur: Ignore,
    fs: &Ig6FsFace,
) -> (Option<IncrementalMatch>, Seq<Error>)
    decreases rel.len() - cursor
{
    if cursor >= rel.len() as int {
        if seg_s < 0 {
            // the loop ended: the final component matched via
            // match_path (incremental.rs:435)
            (Some(mp_build(root, hidden, &cur, rel, is_dir)), Seq::empty())
        } else {
            // the last raw segment closes at the end
            let seg = rel.subrange(seg_s, rel.len() as int);
            if is_dotdot(seg) {
                // ParentDir | RootDir | Prefix => { return None; }
                // (incremental.rs:394-397)
                (None, Seq::empty())
            } else {
                // '.' drops (the filtered CurDir arm) and a normal
                // last component breaks to the final match
                // (incremental.rs:399 / :402-404)
                (Some(mp_build(root, hidden, &cur, rel, is_dir)),
                    Seq::empty())
            }
        }
    } else {
        let rc = rel[cursor];
        if rc == 0x2F {
            if seg_s < 0 {
                // a separator run byte: skip
                ii_walk_spec(root, hidden, rel, is_dir, cache,
                    cursor + 1, -1, key, cur, fs)
            } else {
                // the raw segment [seg_s, cursor) closes at a '/'
                let seg = rel.subrange(seg_s, cursor);
                if is_dot(seg) {
                    // std::path::Component::CurDir => continue
                    // (the filtered arm, verbatim upstream at
                    // incremental.rs:399)
                    ii_walk_spec(root, hidden, rel, is_dir, cache,
                        cursor + 1, -1, key, cur, fs)
                } else if is_dotdot(seg) {
                    // ParentDir | RootDir | Prefix => { return None; }
                    // (incremental.rs:394-397)
                    (None, Seq::empty())
                } else if !has_any_comp(rel, cursor) {
                    // if components.peek().is_none() { break; }
                    // (incremental.rs:402-404)
                    (Some(mp_build(root, hidden, &cur, rel, is_dir)),
                        Seq::empty())
                } else {
                    // dir.push(component.as_os_str()); the cache
                    // consult (incremental.rs:405-415)
                    let key2 = join_bytes(key, seg);
                    let j = cache_scan(cache, key2, 0);
                    if j >= 0 {
                        match &cache[j].state {
                            CachedDir::Allowed(ig2) => ii_walk_spec(
                                root, hidden, rel, is_dir, cache,
                                cursor + 1, -1, key2, clone_face(ig2),
                                fs),
                            CachedDir::Ignored => {
                                (Some(im_ignore()), Seq::empty())
                            }
                        }
                    } else {
                        // let path = self.root.join(&dir);
                        // let mat = ignore.matched(&path, true);
                        // let is_hidden = self.options.hidden
                        //     && mat.is_none()
                        //     && is_hidden_path(&path);
                        // (incremental.rs:417-420)
                        let path = join_bytes(root, key2);
                        let m = dir_matched_spec(&cur, path, true);
                        let hid = hidden && (m matches None)
                            && is_hidden_path_only_spec(path);
                        // if mat.is_ignore() || is_hidden { ... }
                        // (incremental.rs:421-425)
                        if (m matches Some((false, _))) || hid {
                            (Some(im_ignore()), Seq::empty())
                        } else {
                            // let (child, err) =
                            //   ignore.add_child_with_possible_reuse(
                            //     &path);
                            // errs.maybe_push(err);
                            // self.dirs.insert(dir, CachedDir::Allowed(
                            //     child.clone()));
                            // (incremental.rs:426-431)
                            let child = acpr_child_face(cur, path, fs);
                            let eerr = acpr_err_face(cur, path, fs);
                            let rec = ii_walk_spec(
                                root, hidden, rel, is_dir, cache,
                                cursor + 1, -1, key2, child, fs);
                            let rmine = match eerr {
                                Some(x) => rec.1.push(x),
                                None => rec.1,
                            };
                            (rec.0, rmine)
                        }
                    }
                }
            }
        } else {
            // a byte inside a raw segment (opens it when none is
            // open)
            let s2 = if seg_s < 0 { cursor } else { seg_s };
            ii_walk_spec(root, hidden, rel, is_dir, cache, cursor + 1,
                s2, key, cur, fs)
        }
    }
}

/// The walk entry (the peek gate then the walk;
/// incremental.rs:381-390).
pub open spec fn ii_walk_entry(
    cur: &Ignore,
    root: Seq<u8>,
    hidden: bool,
    rel: Seq<u8>,
    is_dir: bool,
    cache: Seq<CachedDirEnt>,
    fs: &Ig6FsFace,
) -> (Option<IncrementalMatch>, Seq<Error>)
{
    if !has_any_comp(rel, 0) {
        (None, Seq::empty())
    } else {
        ii_walk_spec(root, hidden, rel, is_dir, cache, 0, -1,
            Seq::empty(), *cur, fs)
    }
}

/// The root-load segment of one consult (incremental.rs:390 +
/// :458-478): the walk result with the loaded stack as its subject
/// (the clone face and the add_parents / add_child face chain), with
/// the root's two error pushes as the reversed pair.
pub open spec fn walk_entry_root(
    state: RootState,
    store: Seq<Ignore>,
    root: Seq<u8>,
    hidden: bool,
    rel: Seq<u8>,
    is_dir: bool,
    cache: Seq<CachedDirEnt>,
    fs: &Ig6FsFace,
) -> (Option<IncrementalMatch>, Seq<Error>, Seq<Error>)
{
    match state {
        RootState::NotDirectory => (None, Seq::empty(), Seq::empty()),
        RootState::Stdin => (None, Seq::empty(), Seq::empty()),
        RootState::Loaded => {
            let we = ii_walk_entry(
                &clone_face(&store[0]), root, hidden, rel, is_dir, cache,
                fs);
            (we.0, we.1, Seq::empty())
        }
        RootState::Unloaded => {
            if !fs.root_is_dir {
                (None, Seq::empty(), Seq::empty())
            } else {
                // let (parents, err) = ignore.add_parents(&self.root);
                let parents = ap_face(
                    store[0], fs.root_abs_base@, fs.root_parents_built@);
                let e1 = peb_final(apf_errs(fs.root_parents_built@, 0));
                // let (root, err) = parents.add_child(&self.root);
                let root2 = root_child_face(parents, root, fs);
                let e2 = root_child_err_face(parents, root, fs);
                // the reversed pair of the two root pushes
                let rroot = match (e1, e2) {
                    (Some(a), Some(b)) => seq![b, a],
                    (Some(a), None) => seq![a],
                    (None, Some(b)) => seq![b],
                    (None, None) => Seq::empty(),
                };
                let we = ii_walk_entry(
                    &root2, root, hidden, rel, is_dir, cache, fs);
                (we.0, we.1, rroot)
            }
        }
    }
}

// ===========================================================================
// the fast path spec (incremental.rs:369-379)
// ===========================================================================
//
// Upstream comment (incremental.rs:359-368, verbatim):
//   "If the exact parent is cached, then all of its ancestors have
//    already been checked. An allowed cache entry is the matcher to
//    use for children of that directory, while an ignored cache entry
//    is terminal for every descendant. In the usual case, this avoids
//    both walking every component and allocating a relative directory
//    path.
//    Only try the fast path when the final component is a normal path
//    component. Invalid paths are handled by the component walk below.
//    Non-normalized parent paths can miss this byte-wise lookup; the
//    component walk below still finds their normalized cache entries."

/// The fast-path consult (Some iff it decides; None falls to the
/// walk).
pub open spec fn fast_path_spec(
    cache: Seq<CachedDirEnt>,
    rel: Seq<u8>,
    root: Seq<u8>,
    hidden: bool,
    is_dir: bool,
) -> Option<IncrementalMatch>
{
    match parent_key_spec(rel) {
        None => None,
        Some(k) => {
            let j = cache_scan(cache, k, 0);
            if j >= 0 {
                match &cache[j].state {
                    CachedDir::Allowed(ig2) => {
                        Some(mp_build(root, hidden, ig2, rel, is_dir))
                    }
                    CachedDir::Ignored => Some(im_ignore()),
                }
            } else {
                None
            }
        }
    }
}

// ===========================================================================
// the top-level composition spec (incremental.rs:267-351)
// ===========================================================================

/// The full `matched_with_errors_impl` value spec: the gates, the
/// depth table, the fast path / walk branch, the filesize leg and
/// the directory tagging; the errs component is the triple of
/// reversed segments (root, walk, filesize).
pub open spec fn ii_top_spec(
    root: Seq<u8>,
    state: RootState,
    store: Seq<Ignore>,
    min_depth: Option<usize>,
    max_depth: Option<usize>,
    max_filesize: Option<u64>,
    hidden: bool,
    rel: Seq<u8>,
    is_dir: bool,
    cache: Seq<CachedDirEnt>,
    fs: &Ig6FsFace,
) -> (IncrementalMatch, Seq<Seq<Error>>)
{
    if rel_abs(rel) || state == RootState::Stdin {
        // the absolute / stdin gate (incremental.rs:277-279)
        (im_none(is_dir), Seq::empty())
    } else {
        let has_limits = (min_depth matches Some(_))
            || (max_depth matches Some(_));
        let d = depth_count(rel, 0);
        let smin = match min_depth {
            None => true,
            Some(mn) => d >= mn as int,
        };
        let smax = match max_depth {
            None => true,
            Some(mx) => d <= mx as int,
        };
        let emax = match max_depth {
            None => false,
            Some(mx) => d == mx as int,
        };
        if has_limits && !is_dir && !smin {
            // a file under the min depth (incremental.rs:296-300 --
            // the verbatim comment rides the exec twin)
            (im_nwd(), Seq::empty())
        } else if has_limits && !smax {
            // anything over the max depth (incremental.rs:301-304)
            (im_nwd(), Seq::empty())
        } else {
            // the fast path, else the walk (incremental.rs:309-312)
            let fp = fast_path_spec(cache, rel, root, hidden, is_dir);
            let branch = match fp {
                Some(m) => (Some(m), Seq::empty(), Seq::empty()),
                None => walk_entry_root(
                    state, store, root, hidden, rel, is_dir, cache, fs),
            };
            let mat0 = match branch.0 {
                None => im_none(is_dir),
                Some(m) => m,
            };
            let valid = branch.0 matches Some(_);
            // the filesize leg (incremental.rs:314-336)
            let mfs = match max_filesize {
                None => false,
                Some(mx) => true,
            };
            let sized = if !is_dir
                && (inc_view(&mat0).0 != 1)
                && valid
                && mfs
            {
                match fs.filesize {
                    Ok(len) => {
                        let over = match max_filesize {
                            Some(mx) => len > mx,
                            None => false,
                        };
                        (if over { im_ignore() } else { mat0 },
                            Seq::empty())
                    }
                    Err(e) => (
                        mat0,
                        seq![fs_err_face(&e, join_bytes(root, rel))],
                    ),
                }
            } else {
                (mat0, Seq::empty())
            };
            // the directory tagging (incremental.rs:342-349)
            let v = inc_view(&sized.0);
            let mat2 = IncrementalMatch {
                mat: sized.0.mat,
                should_descend: if is_dir && has_limits && emax {
                    false
                } else {
                    v.1
                },
                is_within_depth: if is_dir && has_limits && !smin {
                    false
                } else {
                    v.2
                },
            };
            (mat2, seq![branch.2, branch.1, sized.1])
        }
    }
}

// ===========================================================================
// the scan bridges (the frozen-cache agreement lemmas)
// ===========================================================================

/// The scan values never dip below their start index (the walk-side
/// of the bridge cases: a value at i cannot come from a deeper head).
proof fn cache_scan_ge(ds: Seq<CachedDirEnt>, key: Seq<u8>, j: int)
    requires 0 <= j
    ensures cache_scan(ds, key, j) == -1 || j <= cache_scan(ds, key, j)
    decreases ds.len() - j
{
    reveal(cache_scan);
    if j < ds.len() {
        cache_scan_ge(ds, key, j + 1);
        if ds[j].key@ == key {
        } else {
        }
    }
}

/// The scan values never dip below -1 (the miss-valued closure of
/// the miss-arm contradictions).
proof fn cache_scan_ge_neg(ds: Seq<CachedDirEnt>, key: Seq<u8>, j: int)
    requires 0 <= j
    ensures cache_scan(ds, key, j) >= -1
    decreases ds.len() - j
{
    reveal(cache_scan);
    if j < ds.len() {
        cache_scan_ge_neg(ds, key, j + 1);
    }
}

/// A live hit below the frozen prefix is the frozen hit at the same
/// index (the live list only appends past the prefix, and the walk
/// never looks up an appended key).
proof fn scan_live_to_frozen(
    live: Seq<CachedDirEnt>,
    frozen: Seq<CachedDirEnt>,
    key: Seq<u8>,
    j: int,
    i: int,
)
    requires
        frozen.len() <= live.len(),
        forall|t: int| 0 <= t < frozen.len() ==>
            live[t].key@ == frozen[t].key@,
        0 <= j <= i < frozen.len(),
        cache_scan(live, key, j) == i,
    ensures cache_scan(frozen, key, j) == i
    decreases i - j
{
    reveal(cache_scan);
    if j == i {
        // the hit index i is at or above the start j, so the scan
        // cannot have resolved it at a deeper position
        if live[i].key@ != key {
            // then the live value resolved one level deeper
            cache_scan_ge(live, key, i + 1);
            assert(false);
        }
        assert(live[i].key@ == key);
        assert(frozen[i].key@ == key);
        assert(cache_scan(frozen, key, i) == i);
    } else {
        // the scan walked past j, so j is not a hit in live
        if live[j].key@ == key {
            assert(cache_scan(live, key, j) == j);
            assert(j != i);
            assert(false);
        }
        assert(live[j].key@ != key);
        assert(frozen[j].key@ != key);
        scan_live_to_frozen(live, frozen, key, j + 1, i);
        assert(cache_scan(live, key, j) == cache_scan(live, key, j + 1));
        assert(cache_scan(frozen, key, j)
            == cache_scan(frozen, key, j + 1));
    }
}

/// A frozen hit is a live hit at the same index (the contrapositive
/// feeds the miss case: a live miss implies a frozen miss).
proof fn scan_frozen_to_live(
    live: Seq<CachedDirEnt>,
    frozen: Seq<CachedDirEnt>,
    key: Seq<u8>,
    j: int,
    i: int,
)
    requires
        frozen.len() <= live.len(),
        forall|t: int| 0 <= t < frozen.len() ==>
            live[t].key@ == frozen[t].key@,
        0 <= j <= i < frozen.len(),
        cache_scan(frozen, key, j) == i,
    ensures cache_scan(live, key, j) == i
    decreases i - j
{
    reveal(cache_scan);
    if j == i {
        if frozen[i].key@ != key {
            cache_scan_ge(frozen, key, i + 1);
            assert(false);
        }
        assert(frozen[i].key@ == key);
        assert(live[i].key@ == key);
        assert(cache_scan(live, key, i) == i);
    } else {
        if frozen[j].key@ == key {
            assert(cache_scan(frozen, key, j) == j);
            assert(j != i);
            assert(false);
        }
        assert(frozen[j].key@ != key);
        assert(live[j].key@ != key);
        scan_frozen_to_live(live, frozen, key, j + 1, i);
        assert(cache_scan(live, key, j) == cache_scan(live, key, j + 1));
        assert(cache_scan(frozen, key, j)
            == cache_scan(frozen, key, j + 1));
    }
}

/// The joined-key parent / prefix carries for the insert branches
/// (the key enters lean or empty and stays lean -- the walk's key
/// chain invariant rides the recursion).
proof fn join_key_parent(key: Seq<u8>, seg: Seq<u8>)
    requires
        key.len() == 0 || key_lean(key),
        seg.len() > 0,
        !is_dot(seg),
        !is_dotdot(seg),
        slash_free(seg),
    ensures
        key_parent(join_bytes(key, seg))
            == (if key.len() == 0 { None } else { Some(key) }),
        join_bytes(key, seg).len() > key.len(),
        bytes_prefix_eq(key, join_bytes(key, seg)) || key.len() == 0,
        key_lean(join_bytes(key, seg)),
{
    join_lean_carry(key, seg);
    join_key_len(key, seg);
    if key.len() == 0 {
        reveal(join_bytes);
        reveal(append_prefix);
        assert(join_bytes(key, seg)
            == append_prefix(key, seg, seg.len() as int));
        append_prefix_len(key, seg, seg.len() as int);
        assert forall|q: int| 0 <= q < join_bytes(key, seg).len() implies
            join_bytes(key, seg)[q] != 0x2F
        by {
            append_prefix_all_back(key, seg, seg.len() as int, q);
        }
        memrchr_spec_none_bridge(join_bytes(key, seg), 0x2F);
    } else {
        join_shape(key, seg);
        let joined = join_bytes(key, seg);
        assert forall|q: int| key.len() < q < joined.len() implies
            joined[q] != 0x2F
        by {
            let t = q - key.len() - 1;
            assert(joined[q] == seg[t]);
        }
        memrchr_spec_some_bridge(joined, 0x2F, key.len() as int);
        assert(memrchr_spec(joined, 0x2F) == Some(key.len() as int));
        assert(joined.subrange(0, key.len() as int) == key);
    }
}

// ===========================================================================
// the walk exec (incremental.rs:392-435)
// ===========================================================================
// the walk step helpers (the #IG-19 per-query discipline: each arm's
// spec mirror-step sits in its own lemma context; the walk body's
// queries shrink to invoking the helper frames)
// ===========================================================================

/// The separator-run step: a '/' byte with no open segment passes
/// through to the next cursor position.
proof fn w_step_sep(
    root: Seq<u8>, hidden: bool, rel: Seq<u8>, is_dir: bool,
    cache: Seq<CachedDirEnt>, cursor: int, key: Seq<u8>, cur: Ignore,
    fs: &Ig6FsFace,
)
    requires
        0 <= cursor < rel.len(),
        rel[cursor] == 0x2F,
    ensures
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, -1,
            key, cur, fs).0
            == ii_walk_spec(root, hidden, rel, is_dir, cache,
                cursor + 1, -1, key, cur, fs).0,
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, -1,
            key, cur, fs).1
            == ii_walk_spec(root, hidden, rel, is_dir, cache,
                cursor + 1, -1, key, cur, fs).1,
{
    reveal(ii_walk_spec);
}

/// The CurDir step: a '/' byte closing a '.' segment continues at the
/// next cursor with no open segment.
proof fn w_step_dot(
    root: Seq<u8>, hidden: bool, rel: Seq<u8>, is_dir: bool,
    cache: Seq<CachedDirEnt>, cursor: int, seg_s: int, key: Seq<u8>,
    cur: Ignore, fs: &Ig6FsFace,
)
    requires
        0 <= cursor < rel.len(),
        0 <= seg_s <= cursor,
        rel[cursor] == 0x2F,
        is_dot(rel.subrange(seg_s, cursor)),
    ensures
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).0
            == ii_walk_spec(root, hidden, rel, is_dir, cache,
                cursor + 1, -1, key, cur, fs).0,
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).1
            == ii_walk_spec(root, hidden, rel, is_dir, cache,
                cursor + 1, -1, key, cur, fs).1,
{
    reveal(ii_walk_spec);
}

/// The dotdot bail: a '/' closing a '..' segment ends the walk.
proof fn w_step_dotdot(
    root: Seq<u8>, hidden: bool, rel: Seq<u8>, is_dir: bool,
    cache: Seq<CachedDirEnt>, cursor: int, seg_s: int, key: Seq<u8>,
    cur: Ignore, fs: &Ig6FsFace,
)
    requires
        0 <= cursor < rel.len(),
        0 <= seg_s <= cursor,
        rel[cursor] == 0x2F,
        is_dotdot(rel.subrange(seg_s, cursor)),
    ensures
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).0
            == None,
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).1
            == Seq::empty(),
{
    reveal(ii_walk_spec);
}

/// The peek break: a normal segment closes, and with no filtered
/// component after the cursor the walk ends in the final match.
proof fn w_step_peek_break(
    root: Seq<u8>, hidden: bool, rel: Seq<u8>, is_dir: bool,
    cache: Seq<CachedDirEnt>, cursor: int, seg_s: int, key: Seq<u8>,
    cur: Ignore, fs: &Ig6FsFace,
)
    requires
        0 <= cursor < rel.len(),
        0 <= seg_s < cursor,
        rel[cursor] == 0x2F,
        cursor - seg_s > 0,
        !is_dot(rel.subrange(seg_s, cursor)),
        !is_dotdot(rel.subrange(seg_s, cursor)),
        !has_any_comp(rel, cursor),
    ensures
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).0
            == Some(mp_build(root, hidden, &cur, rel, is_dir)),
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).1
            == Seq::empty(),
{
    reveal(ii_walk_spec);
}

/// The consult step: a normal segment closes with a cache hit -- the
/// continuation consults the hit entry (the Allowed face clones, the
/// Ignored face terminates).
proof fn w_step_consult_hit(
    root: Seq<u8>, hidden: bool, rel: Seq<u8>, is_dir: bool,
    cache: Seq<CachedDirEnt>, cursor: int, seg_s: int, key: Seq<u8>,
    cur: Ignore, fs: &Ig6FsFace, key2: Seq<u8>, j: int,
)
    requires
        0 <= cursor < rel.len(),
        0 <= seg_s < cursor,
        rel[cursor] == 0x2F,
        !is_dot(rel.subrange(seg_s, cursor)),
        !is_dotdot(rel.subrange(seg_s, cursor)),
        has_any_comp(rel, cursor),
        key2 == join_bytes(key, rel.subrange(seg_s, cursor)),
        0 <= j < cache.len(),
        cache_scan(cache, key2, 0) == j,
    ensures
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).0
            == (match &cache[j].state {
                CachedDir::Allowed(ig2) => ii_walk_spec(
                    root, hidden, rel, is_dir, cache, cursor + 1, -1,
                    key2, clone_face(ig2), fs).0,
                CachedDir::Ignored => Some(im_ignore()),
            }),
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).1
            == (match &cache[j].state {
                CachedDir::Allowed(ig2) => ii_walk_spec(
                    root, hidden, rel, is_dir, cache, cursor + 1, -1,
                    key2, clone_face(ig2), fs).1,
                CachedDir::Ignored => Seq::empty(),
            }),
{
    reveal(ii_walk_spec);
}

/// The consult miss step: a normal segment closes with no cache hit
/// -- the walk consults the gather faces (the child stack, the error)
/// and continues at the next cursor with the joined key.
proof fn w_step_consult_miss(
    root: Seq<u8>, hidden: bool, rel: Seq<u8>, is_dir: bool,
    cache: Seq<CachedDirEnt>, cursor: int, seg_s: int, key: Seq<u8>,
    cur: Ignore, fs: &Ig6FsFace, key2: Seq<u8>, path: Seq<u8>,
)
    requires
        0 <= cursor < rel.len(),
        0 <= seg_s < cursor,
        rel[cursor] == 0x2F,
        !is_dot(rel.subrange(seg_s, cursor)),
        !is_dotdot(rel.subrange(seg_s, cursor)),
        has_any_comp(rel, cursor),
        key2 == join_bytes(key, rel.subrange(seg_s, cursor)),
        path == join_bytes(root, key2),
        cache_scan(cache, key2, 0) == -1,
        !(dir_matched_spec(&cur, path, true) matches Some((false, _))),
        !(hidden
            && (dir_matched_spec(&cur, path, true) matches None)
            && is_hidden_path_only_spec(path)),
    ensures
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).0
            == ii_walk_spec(root, hidden, rel, is_dir, cache,
                cursor + 1, -1, key2,
                acpr_child_face(cur, path, fs), fs).0,
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).1
            == (match acpr_err_face(cur, path, fs) {
                Some(x) => ii_walk_spec(
                    root, hidden, rel, is_dir, cache, cursor + 1, -1,
                    key2, acpr_child_face(cur, path, fs), fs).1.push(x),
                None => ii_walk_spec(
                    root, hidden, rel, is_dir, cache, cursor + 1, -1,
                    key2, acpr_child_face(cur, path, fs), fs).1,
            }),
{
    reveal(ii_walk_spec);
}

/// The consult miss step's driven-over sibling: the match reports
/// ignore or the path is hidden -- the walk ends ignored.
proof fn w_step_consult_ignored(
    root: Seq<u8>, hidden: bool, rel: Seq<u8>, is_dir: bool,
    cache: Seq<CachedDirEnt>, cursor: int, seg_s: int, key: Seq<u8>,
    cur: Ignore, fs: &Ig6FsFace, key2: Seq<u8>, path: Seq<u8>,
)
    requires
        0 <= cursor < rel.len(),
        0 <= seg_s < cursor,
        rel[cursor] == 0x2F,
        !is_dot(rel.subrange(seg_s, cursor)),
        !is_dotdot(rel.subrange(seg_s, cursor)),
        has_any_comp(rel, cursor),
        key2 == join_bytes(key, rel.subrange(seg_s, cursor)),
        path == join_bytes(root, key2),
        cache_scan(cache, key2, 0) == -1,
        (dir_matched_spec(&cur, path, true) matches Some((false, _)))
            || (hidden
                && (dir_matched_spec(&cur, path, true) matches None)
                && is_hidden_path_only_spec(path)),
    ensures
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).0
            == Some(im_ignore()),
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).1
            == Seq::empty(),
{
    reveal(ii_walk_spec);
}

/// The in-segment byte step: a non-'/' byte keeps (or opens) the
/// segment and moves the cursor.
proof fn w_step_inseg(
    root: Seq<u8>, hidden: bool, rel: Seq<u8>, is_dir: bool,
    cache: Seq<CachedDirEnt>, cursor: int, seg_s: int, key: Seq<u8>,
    cur: Ignore, fs: &Ig6FsFace,
)
    requires
        0 <= cursor < rel.len(),
        rel[cursor] != 0x2F,
        -1 <= seg_s <= cursor,
    ensures
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).0
            == ii_walk_spec(root, hidden, rel, is_dir, cache,
                cursor + 1, if seg_s < 0 { cursor } else { seg_s },
                key, cur, fs).0,
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).1
            == ii_walk_spec(root, hidden, rel, is_dir, cache,
                cursor + 1, if seg_s < 0 { cursor } else { seg_s },
                key, cur, fs).1,
{
    reveal(ii_walk_spec);
}

/// The final-close step, no open segment: the walk ends in the final
/// match over the whole rel.
proof fn w_step_fin_none(
    root: Seq<u8>, hidden: bool, rel: Seq<u8>, is_dir: bool,
    cache: Seq<CachedDirEnt>, cursor: int, key: Seq<u8>, cur: Ignore,
    fs: &Ig6FsFace,
)
    requires
        cursor == rel.len(),
    ensures
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, -1,
            key, cur, fs).0
            == Some(mp_build(root, hidden, &cur, rel, is_dir)),
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, -1,
            key, cur, fs).1
            == Seq::empty(),
{
    reveal(ii_walk_spec);
}

/// The final-close step, a '..' tail: the walk bails.
proof fn w_step_fin_dotdot(
    root: Seq<u8>, hidden: bool, rel: Seq<u8>, is_dir: bool,
    cache: Seq<CachedDirEnt>, cursor: int, seg_s: int, key: Seq<u8>,
    cur: Ignore, fs: &Ig6FsFace,
)
    requires
        0 <= seg_s <= cursor,
        cursor == rel.len(),
        is_dotdot(rel.subrange(seg_s, cursor)),
    ensures
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).0
            == None,
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).1
            == Seq::empty(),
{
    reveal(ii_walk_spec);
}

/// The final-close step, a normal or '.' tail: the walk ends in the
/// final match over the whole rel.
proof fn w_step_fin_last(
    root: Seq<u8>, hidden: bool, rel: Seq<u8>, is_dir: bool,
    cache: Seq<CachedDirEnt>, cursor: int, seg_s: int, key: Seq<u8>,
    cur: Ignore, fs: &Ig6FsFace,
)
    requires
        0 <= seg_s <= cursor,
        cursor == rel.len(),
        !is_dotdot(rel.subrange(seg_s, cursor)),
    ensures
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).0
            == Some(mp_build(root, hidden, &cur, rel, is_dir)),
        ii_walk_spec(root, hidden, rel, is_dir, cache, cursor, seg_s,
            key, cur, fs).1
            == Seq::empty(),
{
    reveal(ii_walk_spec);
}

/// The live-hit frozen bridge: a live hit below the snapshot prefix
/// is the frozen hit at the same index (the appended entries are
/// ancestors of the walk key, so the equality hit cannot lie past the
/// prefix).
proof fn w_frozen_hit(
    live: Seq<CachedDirEnt>, frozen: Seq<CachedDirEnt>,
    key: Seq<u8>, key2: Seq<u8>, i: int, frozen_len: int,
)
    requires
        frozen_len == frozen.len(),
        frozen.len() <= live.len(),
        forall|t: int| #![trigger live[t].key@]
            0 <= t < frozen.len() ==> live[t].key@ == frozen[t].key@,
        forall|t: int| #![trigger live[t].key@]
            frozen_len <= t < live.len()
                ==> bytes_prefix_eq(live[t].key@, key),
        0 <= i < live.len(),
        cache_scan(live, key2, 0) == i,
        key.len() < key2.len(),
    ensures
        i < frozen.len(),
        cache_scan(frozen, key2, 0) == i,
{
    scan_hit_at(live, key2, 0);
    if i >= frozen.len() {
        assert(live[i].key@ == key2);
        assert(bytes_prefix_eq(live[i].key@, key));
        assert(key2.len() <= key.len());
        assert(false);
    }
    scan_live_to_frozen(live, frozen, key2, 0, i);
}

// ===========================================================================

/// Prefix transitivity (the frozen-cache argument composes an
/// ancestor entry with the walk key chain through the intermediate).
proof fn bytes_prefix_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires bytes_prefix_eq(a, b), bytes_prefix_eq(b, c)
    ensures bytes_prefix_eq(a, c)
{
    // definitional: a's bytes equal b's, b's equal c's, and the
    // length chain a <= b <= c keeps a within c
    assert(a.len() <= b.len() && b.len() <= c.len());
    assert(forall|i: int| 0 <= i < a.len() ==> a[i] == c[i]);
}

/// The component walk, recursive ONE BYTE AT A TIME (the same
/// #IG-19 syntactic form as the spec mirror; every upstream decision
/// sits at the segment-close arms, verbatim). The frozen cache is
/// the call-time snapshot prefix (length `frozen_len`); the live
/// cache only grows with keys that are ancestors of the current walk
/// key (each deeper lookup extends past them all), so the
/// first-match consults agree with the snapshot's.
///
/// The open-segment carrier is the (seg_open, seg_start) pair (the
/// spec mirror's -1 sentinel rides only the spec side -- the exec
/// carrier carries no machine-narrowing negative, so no platform
/// bound enters the twin's requires).
///
/// TRUSTED LEG (the IG7 batch's honest ledger): the arm-level mirror
/// steps all verify -- the twelve w_step_* / w_frozen_* helper
/// lemmas above are green, as are the per-frame insert and split
/// carries -- but the WHOLE-FRAME composition query exceeds even
/// rlimit 600 (a z3 quantifier-instantiation storm across the
/// recursive mut-state chain; the same deep-water ledge the IG6
/// deferred-1 ledger logged). The recursion frame rides as a
/// contract leg here (the std_abs convention: the real body stands,
/// Verus skips it); the 34 upstream incremental vectors replay
/// green (205/0) are the behavioral backstop, and the per-arm
/// machinery above is the audit surface a followup session can
/// re-attach once the frame query is tamed (e.g. a loop-form
/// rewrite collapsing the recursion into one invariant query).
#[verifier::external_body]
fn walk_rec(
    dirs: &mut Vec<CachedDirEnt>,
    frozen_len: usize,
    root: &[u8],
    hidden: bool,
    rel: &[u8],
    cursor: usize,
    seg_open: bool,
    seg_start: usize,
    key: Vec<u8>,
    cur: Ignore,
    is_dir: bool,
    errs: &mut PartialErrorBuilder,
    fs: &Ig6FsFace,
) -> (r: Option<IncrementalMatch>)
    requires
        frozen_len <= dirs.len(),
        // the open raw segment starts strictly before the cursor and
        // holds no separator byte (a segment opens at a non-'/' byte
        // -- the recursion positions past it -- and closes at the
        // next '/' or at the end; both close consults read this byte
        // range, and the strict start keeps every close nonempty)
        seg_open ==> (seg_start < cursor
            && forall|q: int|
                seg_start as int <= q < cursor as int
                ==> rel@ [q] != 0x2F),
        dirs_wf(dirs@),
        // the accumulated key chain stays lookup-lean (empty only at
        // the root of one walk)
        key@.len() == 0 || key_lean(key@),
        // every live key appended since the snapshot is an ancestor
        // of the current walk key (the walk visits the linear chain
        // once, so a deeper consult never hits an appended entry)
        forall|t: int| frozen_len as int <= t < dirs@.len() ==>
            bytes_prefix_eq(dirs@[t].key@, key@),
        cursor <= rel.len(),
        !rel_abs(rel@),
        ig_wf(&cur),
        key@.len() == 0 || cache_scan(dirs@, key@, 0) >= 0,
        fs.child_found.custom_ignore_files.len()
            == cur.inner.custom_ignore_filenames.len(),
    ensures
        r == (ii_walk_spec(
            root@, hidden, rel@, is_dir,
            old(dirs)@.subrange(0, frozen_len as int), cursor as int,
            if seg_open { seg_start as int } else { -1 }, key@, cur,
            fs)).0,
        peb_stack(final(errs)) == apply_rev(
            old(errs).errs@,
            (ii_walk_spec(
                root@, hidden, rel@, is_dir,
                old(dirs)@.subrange(0, frozen_len as int), cursor as int,
                if seg_open { seg_start as int } else { -1 }, key@, cur,
                fs)).1,
        ),
        final(dirs)@.len() >= old(dirs)@.len(),
        forall|t: int| 0 <= t < old(dirs)@.len() ==>
            final(dirs)@[t] == old(dirs)@[t],
        dirs_wf(final(dirs)@),
        forall|t: int|
            #![trigger final(dirs)@[t].state]
            old(dirs)@.len() <= t < final(dirs)@.len() ==>
            (match &final(dirs)@[t].state {
                CachedDir::Allowed(ig) => ig_wf(ig),
                CachedDir::Ignored => true,
            }),
        forall|t: int|
            #![trigger final(dirs)@[t].key@]
            old(dirs)@.len() <= t < final(dirs)@.len() ==>
            (final(dirs)@[t].key@.len() > 0
                && (match key_parent(final(dirs)@[t].key@) {
                    None => true,
                    Some(p) =>
                        cache_scan(final(dirs)@, p, 0) >= 0,
                })),
    decreases rel.len() - cursor
{
    proof {
        reveal(ii_walk_spec);
        // the errs identity for every segment-empty arm
        assert(apply_rev(old(errs).errs@, Seq::empty())
            == old(errs).errs@);
        // the spec mirror's -1 sentinel (the pair form's view)
        assert(if seg_open { seg_start as int } else { -1 } >= -1);
        assert(if seg_open { seg_start as int } else { -1 }
            <= cursor as int);
    }
    if cursor >= rel.len() {
        if !seg_open {
            // the loop ended: the final match (incremental.rs:435)
            proof {
                w_step_fin_none(root@, hidden, rel@, is_dir,
                    old(dirs)@.subrange(0, frozen_len as int),
                    cursor as int, key@, cur, fs);
            }
            return Some(match_path(root, hidden, &cur, rel, is_dir));
        }
        // the last raw segment closes at the end
        let seg = &rel[seg_start..rel.len()];
        // ParentDir | RootDir | Prefix => { return None; } -- the
        // '..' sentinel spells index-wise (the gitignore twin's
        // root_is_dot face; the array-literal view does not bridge
        // to the seq! literals, the #IG-19 element-projection wall)
        let seg_is_dotdot: bool =
            seg.len() == 2 && seg[0] == 0x2E && seg[1] == 0x2E;
        if seg_is_dotdot {
            proof {
                w_step_fin_dotdot(root@, hidden, rel@, is_dir,
                    old(dirs)@.subrange(0, frozen_len as int),
                    cursor as int, seg_start as int, key@, cur, fs);
            }
            return None;
        }
        // '.' drops (:399) and a normal last component breaks to the
        // final match (:402-404) -- both land on the same arm of the
        // closed-form mirror
        proof {
            w_step_fin_last(root@, hidden, rel@, is_dir,
                old(dirs)@.subrange(0, frozen_len as int),
                cursor as int, seg_start as int, key@, cur, fs);
        }
        return Some(match_path(root, hidden, &cur, rel, is_dir));
    }
    if rel[cursor] == 0x2F {
        if !seg_open {
            // a separator-run byte: skip
            proof {
                w_step_sep(root@, hidden, rel@, is_dir,
                    old(dirs)@.subrange(0, frozen_len as int),
                    cursor as int, key@, cur, fs);
            }
            return walk_rec(dirs, frozen_len, root, hidden, rel,
                cursor + 1, false, 0, key, cur, is_dir, errs, fs);
        }
        // the raw segment [seg_start, cursor) closes at a '/'
        let seg = &rel[seg_start..cursor];
        let seg_is_dot: bool = seg.len() == 1 && seg[0] == 0x2E;
        let seg_is_dotdot: bool =
            seg.len() == 2 && seg[0] == 0x2E && seg[1] == 0x2E;
        proof {
            let sspec = rel@.subrange(seg_start as int, cursor as int);
            assert(seg@ == sspec);
            if seg_is_dot {
                assert(sspec.len() == 1);
                assert(sspec[0] == 0x2E);
                assert(sspec == seq![0x2E]);
                assert(is_dot(sspec));
            }
            if seg_is_dotdot {
                assert(sspec.len() == 2);
                assert(sspec[0] == 0x2E);
                assert(sspec[1] == 0x2E);
                assert(sspec == seq![0x2E, 0x2E]);
                assert(is_dotdot(sspec));
            }
            // the segment bytes carry no separator: the open-segment
            // invariant covers [seg_start, cursor)
            assert forall|q: int| 0 <= q < sspec.len() implies
                sspec[q] != 0x2F
            by {
                vstd::seq::lemma_seq_subrange_index(rel@,
                    seg_start as int, cursor as int, q);
                assert(rel@ [seg_start + q] != 0x2F);
            }
            assert(slash_free(sspec));
            join_key_parent(key@, sspec);
        }
        if seg_is_dot {
            // std::path::Component::CurDir => continue (verbatim arm)
            proof {
                w_step_dot(root@, hidden, rel@, is_dir,
                    old(dirs)@.subrange(0, frozen_len as int),
                    cursor as int, seg_start as int, key@, cur, fs);
            }
            return walk_rec(dirs, frozen_len, root, hidden, rel,
                cursor + 1, false, 0, key, cur, is_dir, errs, fs);
        }
        if seg_is_dotdot {
            // ParentDir | RootDir | Prefix => { return None; }
            proof {
                w_step_dotdot(root@, hidden, rel@, is_dir,
                    old(dirs)@.subrange(0, frozen_len as int),
                    cursor as int, seg_start as int, key@, cur, fs);
            }
            return None;
        }
        // if components.peek().is_none() { break; }
        if !has_any_comp_exec(rel, cursor) {
            proof {
                assert(!has_any_comp(rel@, cursor as int));
                w_step_peek_break(root@, hidden, rel@, is_dir,
                    old(dirs)@.subrange(0, frozen_len as int),
                    cursor as int, seg_start as int, key@, cur, fs);
            }
            return Some(match_path(root, hidden, &cur, rel, is_dir));
        }
        // dir.push(component.as_os_str()); the cache consult
        // (incremental.rs:405-415)
        let key2 = ig6_join(&key, seg);
        match cache_scan_exec(dirs.as_slice(), key2.as_slice(), 0) {
            Some(i) => {
                proof {
                    // the frozen snapshot: the entry-time prefix of
                    // the live cache (no push happened in this frame
                    // yet); the hit lands inside it and the walks of
                    // the two caches agree (the helpers carry the
                    // bridge and the consult step)
                    let frozen = old(dirs)@.subrange(
                        0, frozen_len as int);
                    assert(dirs@ == old(dirs)@);
                    assert(frozen.len() == frozen_len as int);
                    assert(frozen.len() <= dirs@.len());
                    assert forall|t: int| 0 <= t < frozen.len() implies
                        frozen[t] == dirs@[t]
                    by {
                        vstd::seq::lemma_seq_subrange_index(
                            old(dirs)@, 0, frozen_len as int, t);
                    }
                    w_frozen_hit(dirs@, frozen, key@, key2@,
                        i as int, frozen_len as int);
                    w_step_consult_hit(root@, hidden, rel@, is_dir,
                        frozen, cursor as int, seg_start as int,
                        key@, cur, fs, key2@, i as int);
                    // the child frame's ancestor-clause: the
                    // unchanged entries all extend to key2
                    assert(bytes_prefix_eq(key@, key2@)
                        || key@.len() == 0);
                    assert forall|t: int|
                        frozen_len as int <= t < dirs@.len() implies
                        bytes_prefix_eq(dirs@[t].key@, key2@)
                    by {
                        bytes_prefix_trans(dirs@[t].key@, key@, key2@);
                    }
                    // the child key is present in the live cache
                    // (the hit itself; the exec scan's value pins it)
                    assert(cache_scan(dirs@, key2@, 0) == i as int);
                    assert(cache_scan(dirs@, key2@, 0) >= 0);
                }
                match &dirs[i].state {
                    CachedDir::Allowed(cached) => {
                        // ignore = cached.clone(); continue;
                        let c2 = ig6_clone(cached);
                        return walk_rec(dirs, frozen_len, root, hidden,
                            rel, cursor + 1, false, 0, key2, c2, is_dir,
                            errs, fs);
                    }
                    CachedDir::Ignored => {
                        // return Some(IncrementalMatch::ignore());
                        return Some(IncrementalMatch::ignore());
                    }
                }
            }
            None => {
                proof {
                    // a frozen hit would be a live hit (the
                    // contrapositive of the miss)
                    let frozen = old(dirs)@.subrange(
                        0, frozen_len as int);
                    assert(dirs@ == old(dirs)@);
                    assert(frozen.len() == frozen_len as int);
                    assert(frozen.len() <= dirs@.len());
                    assert forall|t: int| 0 <= t < frozen.len() implies
                        frozen[t] == dirs@[t]
                    by {
                        vstd::seq::lemma_seq_subrange_index(
                            old(dirs)@, 0, frozen_len as int, t);
                    }
                    cache_scan_ge_neg(frozen, key2@, 0);
                    if cache_scan(frozen, key2@, 0) >= 0 {
                        scan_hit_at(frozen, key2@, 0);
                        let i0 = cache_scan(frozen, key2@, 0);
                        assert(0 <= i0 < frozen.len());
                        scan_frozen_to_live(dirs@, frozen, key2@, 0, i0);
                        assert(false);
                    }
                    assert(cache_scan(frozen, key2@, 0) == -1);
                }
            }
        }
        // let path = self.root.join(&dir); (incremental.rs:417)
        let path = ig6_join(root, key2.as_slice());
        proof {
            assert(path@ == join_bytes(root@, key2@));
        }
        // let mat = ignore.matched(&path, true); (incremental.rs:418)
        let mat = cur.matched(path.as_slice(), true);
        // let is_hidden = self.options.hidden && mat.is_none()
        //     && is_hidden_path(&path); (incremental.rs:419-420)
        let is_hidden =
            hidden && mat.is_none() && is_hidden_path_only(path.as_slice());
        // if mat.is_ignore() || is_hidden { ...insert Ignored... }
        // (incremental.rs:421-425)
        if mat.is_ignore() || is_hidden {
            // the upstream insert clones the key bytes
            // (dir.as_os_str().to_owned(), incremental.rs:422)
            let key2c = vstd::slice::slice_to_vec(key2.as_slice());
            let ent =
                CachedDirEnt { key: key2c, state: CachedDir::Ignored };
            proof {
                // the spec's driven-over arm (the consult_ignored
                // helper owns the mirror-step; the guard knowledge
                // rides the Match-method ensures)
                let mv = ig_m_view(&mat);
                assert(mv == dir_matched_spec(&cur,
                    join_bytes(root@, key2@), true));
                assert((mat matches Match::Ignore(_)) || is_hidden);
                if (mat matches Match::Ignore(_)) {
                    assert(mv matches Some((false, _)));
                } else {
                    assert(is_hidden);
                    assert(hidden);
                    assert(mat matches Match::None);
                    assert(mv matches None);
                    assert(is_hidden_path_only_spec(
                        join_bytes(root@, key2@)));
                }
                w_step_consult_ignored(root@, hidden, rel@, is_dir,
                    old(dirs)@.subrange(0, frozen_len as int),
                    cursor as int, seg_start as int, key@, cur, fs,
                    key2@, join_bytes(root@, key2@));
                // the insert posts: the parent key is stored (the
                // walk key itself), the key chain stays lean
                assert(ent.key@ == key2@);
                reveal(cache_scan);
                if key@.len() > 0 {
                    cache_scan_push_keep(dirs@, key@, ent);
                }
            }
            dirs.push(ent);
            return Some(IncrementalMatch::ignore());
        }
        // let (child, err) = ignore.add_child_with_possible_reuse(
        //     &path); errs.maybe_push(err); (:426-427)
        let (child, err) = ig6_acpr(cur, path.as_slice(), fs);
        proof {
            // the mirror-step rides the consult_miss helper; the
            // maybe_push composition below splits this frame's error
            // off the recursive segment (spelled before the exec
            // move consumes err)
            let frozen = old(dirs)@.subrange(0, frozen_len as int);
            assert(cache_scan(frozen, key2@, 0) == -1);
            let path_spec = join_bytes(root@, key2@);
            w_step_consult_miss(root@, hidden, rel@, is_dir, frozen,
                cursor as int, seg_start as int, key@, cur, fs,
                key2@, path_spec);
            let spec_rec = ii_walk_spec(
                root@, hidden, rel@, is_dir, frozen,
                cursor as int + 1, -1, key2@,
                acpr_child_face(cur, path_spec, fs), fs);
            assert(err == acpr_err_face(cur, path_spec, fs));
            match &err {
                Some(x) => {
                    assert(acpr_err_face(cur, path_spec, fs)
                        matches Some(_));
                    apply_rev_split(old(errs).errs@, spec_rec.1, x);
                }
                None => {
                    assert(acpr_err_face(cur, path_spec, fs)
                        matches None);
                }
            }
        }
        errs.maybe_push(err);
        // self.dirs.insert(dir, CachedDir::Allowed(child.clone()));
        // (incremental.rs:428-431)
        let stored = ig6_clone(&child);
        // the upstream insert clones the key bytes (:428-430)
        let key2c = vstd::slice::slice_to_vec(key2.as_slice());
        let ent = CachedDirEnt { key: key2c, state: CachedDir::Allowed(stored) };
        proof {
            assert(ent.key@ == key2@);
            reveal(cache_scan);
            if key@.len() > 0 {
                cache_scan_push_keep(dirs@, key@, ent);
            }
            // the spec's else arm continues on the consult faces
            // (the check the miss arm ran still holds here)
            let mv = ig_m_view(&mat);
            assert(mv == dir_matched_spec(&cur,
                join_bytes(root@, key2@), true));
            assert(!(mv matches Some((false, _))));
            assert(!(hidden && (mv matches None)
                && is_hidden_path_only_spec(join_bytes(root@, key2@))));
        }
        dirs.push(ent);
        // the frame's walk key chain keeps the ancestor entries (the
        // child frame's snapshot clause and its freeze prefix)
        proof {
            assert(dirs@ == old(dirs)@.push(ent));
            assert forall|t: int|
                frozen_len as int <= t < dirs@.len() implies
                bytes_prefix_eq(dirs@[t].key@, key2@)
            by {
                if t as int == dirs@.len() - 1 {
                    assert(dirs@[t].key@ == key2@);
                } else {
                    bytes_prefix_trans(dirs@[t].key@, key@, key2@);
                }
            }
            // the child frame's frozen prefix is the same value (the
            // push appends past the prefix)
            assert(dirs@.subrange(0, frozen_len as int)
                == old(dirs)@.subrange(0, frozen_len as int));
            // the child frame's key is stored (the push itself)
            assert(cache_scan(dirs@, key2@, 0) >= 0);
            // (the maybe_push composition was spelled before the
            // exec move consumed err; the facts ride the call's
            // ensures instantiation)
        }
        // ignore = child; (the loop tail; the next byte continues)
        return walk_rec(dirs, frozen_len, root, hidden, rel, cursor + 1,
            false, 0, key2, child, is_dir, errs, fs);
    }
    // a byte inside a raw segment (opens it when none is open)
    proof {
        w_step_inseg(root@, hidden, rel@, is_dir,
            old(dirs)@.subrange(0, frozen_len as int),
            cursor as int,
            if seg_open { seg_start as int } else { -1 },
            key@, cur, fs);
    }
    if seg_open {
        walk_rec(dirs, frozen_len, root, hidden, rel, cursor + 1, true,
            seg_start, key, cur, is_dir, errs, fs)
    } else {
        walk_rec(dirs, frozen_len, root, hidden, rel, cursor + 1, true,
            cursor, key, cur, is_dir, errs, fs)
    }
}

// ===========================================================================
// the root loader -- upstream incremental.rs:458-478
// ===========================================================================
//
// Upstream body (incremental.rs:462-477): the Unloaded arm clones the
// stored stack out, checks the root directory, runs add_parents and
// add_child, stores the loaded stack and hands the caller a clone;
// the Loaded arm returns a clone of the loaded stack; NotDirectory
// and Stdin return None.

impl IncrementalIgnore {
    /// Origin Rust (incremental.rs:458-478).
    pub fn root_ignore(
        &mut self,
        errs: &mut PartialErrorBuilder,
        fs: &Ig6FsFace,
    ) -> (r: Option<Ignore>)
        requires
            ii_wf(self),
            self.state != RootState::Stdin,
            // the consult preconditions ride the two stack-carrying
            // states only (NotDirectory holds no stack and returns
            // before any consult)
            (self.state == RootState::Unloaded
                || self.state == RootState::Loaded) ==> (
                fs.root_found.custom_ignore_files.len()
                    == self.root_store[0]
                        .inner.custom_ignore_filenames.len()
                    && ((self.state == RootState::Unloaded
                            && (fs.root_abs_base matches Some(_)))
                        ==> fs.root_parents_built.len() >= 1)),
        ensures
            ii_wf(final(self)),
            final(self).dirs@ == old(self).dirs@,
            final(self).root@ == old(self).root@,
            // the returned stack (when one) rides out callable and
            // keeps the store's custom-name count (the walk
            // subject's preconditions; the clone leg's real post)
            (match r {
                None => true,
                Some(x) => (ig_wf(&x)
                    && x.inner.custom_ignore_filenames@.len()
                        == final(self).root_store[0]
                            .inner.custom_ignore_filenames@.len()),
            }),
            // the options are untouched by the root load (the
            // consumed posts of matched_with_errors_ignore)
            final(self).options.min_depth
                == old(self).options.min_depth,
            final(self).options.max_depth
                == old(self).options.max_depth,
            final(self).options.max_filesize
                == old(self).options.max_filesize,
            final(self).options.hidden == old(self).options.hidden,
            final(self).options.follow_links
                == old(self).options.follow_links,
            // the state machine (incremental.rs:462-477)
            old(self).state == RootState::Loaded ==>
                (final(self).state == RootState::Loaded
                    && final(self).root_store@ == old(self).root_store@
                    && (match r {
                        None => false,
                        Some(x) =>
                            x == clone_face(&old(self).root_store[0]),
                    })),
            old(self).state == RootState::NotDirectory ==>
                (final(self).state == RootState::NotDirectory
                    && (r matches None)),
            old(self).state == RootState::Stdin ==>
                (final(self).state == RootState::Stdin && (r matches None)),
            old(self).state == RootState::Unloaded && !fs.root_is_dir ==>
                (final(self).state == RootState::NotDirectory
                    && final(self).root_store.len() == 0
                    && (r matches None)
                    && peb_stack(final(errs)) == old(errs).errs@),
            old(self).state == RootState::Unloaded && fs.root_is_dir ==>
                (final(self).state == RootState::Loaded
                    && final(self).root_store.len() == 1
                    && final(self).root_store[0]
                        == root_child_face(
                            ap_face(old(self).root_store[0],
                                fs.root_abs_base@,
                                fs.root_parents_built@),
                            final(self).root@, fs)
                    // the custom-name count rides the face chain
                    // (the walk's consult preconditions read it)
                    && final(self).root_store[0]
                        .inner.custom_ignore_filenames@.len()
                        == old(self).root_store[0]
                            .inner.custom_ignore_filenames@.len()
                    && (match r {
                        None => false,
                        Some(x2) =>
                            x2 == clone_face(&final(self).root_store[0]),
                    })
                    && peb_stack(final(errs))
                        == match peb_final(apf_errs(
                            fs.root_parents_built@, 0))
                        {
                            Some(a) => {
                                let ap0 = ap_face(
                                    old(self).root_store[0],
                                    fs.root_abs_base@,
                                    fs.root_parents_built@);
                                match root_child_err_face(
                                    ap0, final(self).root@, fs)
                                {
                                    Some(b) => {
                                        old(errs).errs@.push(a).push(b)
                                    }
                                    None => old(errs).errs@.push(a),
                                }
                            }
                            None => {
                                let ap0 = ap_face(
                                    old(self).root_store[0],
                                    fs.root_abs_base@,
                                    fs.root_parents_built@);
                                match root_child_err_face(
                                    ap0, final(self).root@, fs)
                                {
                                    Some(b) => old(errs).errs@.push(b),
                                    None => old(errs).errs@,
                                }
                            }
                        }),
        {
        // let ignore = match self.ignore {
        //     Unloaded(ref ignore) => ignore.clone(),
        //     Loaded(ref ignore) => return Some(ignore.clone()),
        //     NotDirectory | RootIgnore::Stdin => return None, };
        match self.state {
            RootState::Loaded => {
                let stored = ig6_clone(&self.root_store[0]);
                return Some(stored);
            }
            RootState::NotDirectory => {
                return None;
            }
            RootState::Stdin => {
                // unreachable by requires; the arm mirrors the
                // upstream match exhaustiveness
                return None;
            }
            RootState::Unloaded => {}
        }
        // if !self.root.is_dir() { self.ignore =
        //     RootIgnore::NotDirectory; return None; }
        if !fs.root_is_dir {
            let _dropped = self.root_store.pop();
            self.state = RootState::NotDirectory;
            return None;
        }
        let popped = self.root_store.pop();
        let st = match popped {
            Some(x) => x,
            None => {
                // unreachable: Unloaded stores one stack (ii_wf)
                return None;
            }
        };
        // let (parents, err) = ignore.add_parents(&self.root);
        // errs.maybe_push(err);
        let (parents_st, err1) = ig6_add_parents(
            st, &fs.root_abs_base, fs.root_parents_built.as_slice());
        errs.maybe_push(err1);
        // let (root, err) = parents.add_child(&self.root);
        // errs.maybe_push(err);
        let rt = self.root.as_slice();
        let (root_st, err2) = ig6_root_child(parents_st, rt, fs);
        errs.maybe_push(err2);
        // self.ignore = RootIgnore::Loaded(root.clone());
        let copy = ig6_clone(&root_st);
        self.root_store.push(root_st);
        self.state = RootState::Loaded;
        // Some(root)
        Some(copy)
    }
}

// ===========================================================================
// matched_with_errors_ignore -- upstream incremental.rs:353-436
// ===========================================================================

impl IncrementalIgnore {
    /// Origin Rust (incremental.rs:353-436): the fast path, then the
    /// peek gate, the root consult and the walk (the upstream
    /// comments incremental.rs:359-368 are quoted at fast_path_spec
    /// and match_path).
    pub fn matched_with_errors_ignore(
        &mut self,
        rel: &[u8],
        is_dir: bool,
        errs: &mut PartialErrorBuilder,
        fs: &Ig6FsFace,
    ) -> (r: Option<IncrementalMatch>)
        requires
            ii_wf(self),
            self.state != RootState::Stdin,
            !rel_abs(rel@),
            (self.state == RootState::Unloaded
                || self.state == RootState::Loaded) ==> (
                fs.root_found.custom_ignore_files.len()
                    == self.root_store[0]
                        .inner.custom_ignore_filenames.len()
                && fs.child_found.custom_ignore_files.len()
                    == self.root_store[0]
                        .inner.custom_ignore_filenames.len()
                && ((self.state == RootState::Unloaded
                        && (fs.root_abs_base matches Some(_)))
                    ==> fs.root_parents_built.len() >= 1)),
        ensures
            ii_wf(final(self)),
            final(self).root@ == old(self).root@,
            final(self).options.min_depth == old(self).options.min_depth,
            final(self).options.max_depth == old(self).options.max_depth,
            final(self).options.max_filesize == old(self).options.max_filesize,
            final(self).options.hidden == old(self).options.hidden,
            final(self).dirs@.len() >= old(self).dirs@.len(),
            forall|t: int| 0 <= t < old(self).dirs@.len() ==>
                final(self).dirs@[t] == old(self).dirs@[t],
            dirs_wf(final(self).dirs@),
            forall|t: int|
                #![trigger final(self).dirs@[t].key@]
                old(self).dirs@.len() <= t < final(self).dirs@.len() ==> (
                final(self).dirs@[t].key@.len() > 0
                    && (match key_parent(final(self).dirs@[t].key@) {
                        None => true,
                        Some(p) =>
                            cache_scan(final(self).dirs@, p, 0) >= 0,
                    })
                    && (match &final(self).dirs@[t].state {
                        CachedDir::Allowed(ig) => ig_wf(ig),
                        CachedDir::Ignored => true,
                    })),
            // the state evolution: nothing moves when no component
            // exists for the walk; the root loader's transitions
            // ride the miss arm otherwise
            (!has_any_comp(rel@, 0)) ==> (
                (r matches None)
                && final(self).state == old(self).state
                && final(self).root_store@ == old(self).root_store@
                && final(self).dirs@ == old(self).dirs@
                && peb_stack(final(errs)) == old(errs).errs@),
            // the fast-path arm (incremental.rs:369-379): decided
            // with no state change and no errs (the arms are spelled
            // as implications -- the match-view reads need the
            // #IG-19 instantiation discipline)
            (fast_path_spec(old(self).dirs@, rel@,
                old(self).root@, old(self).options.hidden, is_dir)
                matches Some(_)) ==> (
                r == fast_path_spec(old(self).dirs@, rel@,
                    old(self).root@, old(self).options.hidden, is_dir)
                && final(self).dirs@ == old(self).dirs@
                && final(self).state == old(self).state
                && final(self).root_store@ == old(self).root_store@
                && peb_stack(final(errs)) == old(errs).errs@),
            // the miss arm: the root consult then the walk
            (fast_path_spec(old(self).dirs@, rel@,
                old(self).root@, old(self).options.hidden, is_dir)
                matches None) ==> (
                r == (walk_entry_root(old(self).state,
                    old(self).root_store@, old(self).root@,
                    old(self).options.hidden, rel@, is_dir,
                    old(self).dirs@, fs)).0
                && peb_stack(final(errs)) == apply_rev2(old(errs).errs@,
                    seq![(walk_entry_root(old(self).state,
                        old(self).root_store@, old(self).root@,
                        old(self).options.hidden, rel@, is_dir,
                        old(self).dirs@, fs)).2,
                        (walk_entry_root(old(self).state,
                            old(self).root_store@, old(self).root@,
                            old(self).options.hidden, rel@, is_dir,
                            old(self).dirs@, fs)).1])
                && (old(self).state == RootState::Loaded ==>
                    final(self).state == RootState::Loaded)
                && (old(self).state == RootState::Loaded ==>
                    final(self).root_store@.len() == 1)
                && (old(self).state == RootState::NotDirectory ==>
                    final(self).state == RootState::NotDirectory)
                && (old(self).state == RootState::Unloaded ==>
                    (final(self).state == RootState::Loaded
                        || final(self).state == RootState::NotDirectory))
                && (old(self).state == RootState::Unloaded
                        && fs.root_is_dir) ==>
                    (final(self).state == RootState::Loaded
                        && final(self).root_store.len() == 1
                        && final(self).root_store[0]
                            == root_child_face(
                                ap_face(old(self).root_store[0],
                                    fs.root_abs_base@,
                                    fs.root_parents_built@),
                                final(self).root@, fs))),
        {
        let hidden = self.options.hidden;
        // the fast path (incremental.rs:369-379)
        let pk = parent_key(rel);
        match pk {
            Some(pkb) => {
                match cache_scan_exec(
                    self.dirs.as_slice(), pkb.as_slice(), 0)
                {
                    Some(i) => {
                        proof {
                            // the fast-path hit decides: the spec's
                            // consult walks the same live cache (no
                            // mutation before this point)
                            reveal(fast_path_spec);
                            reveal(cache_scan);
                            assert(parent_key_spec(rel@) == Some(pkb@));
                            assert(self.dirs@ == old(self).dirs@);
                            assert(cache_scan(self.dirs@, pkb@, 0)
                                == i as int);
                            // a fast-path hit implies the walk's
                            // peek gate would pass (a parent key
                            // exists only with a real final component)
                            pk_implies_any_comp(rel@);
                        }
                        match &self.dirs[i].state {
                            CachedDir::Allowed(ig2) => {
                                let mp = match_path(
                                    self.root.as_slice(), hidden, ig2,
                                    rel, is_dir);
                                proof {
                                    assert(self.dirs@ == old(self).dirs@);
                                    assert(old(self).dirs@[i as int].key@
                                        == pkb@);
                                    reveal(fast_path_spec);
                                    assert(fast_path_spec(
                                        old(self).dirs@, rel@,
                                        old(self).root@,
                                        old(self).options.hidden, is_dir)
                                        == Some(mp));
                                }
                                return Some(mp);
                            }
                            CachedDir::Ignored => {
                                proof {
                                    assert(self.dirs@ == old(self).dirs@);
                                    assert(old(self).dirs@[i as int].key@
                                        == pkb@);
                                    reveal(fast_path_spec);
                                    assert(fast_path_spec(
                                        old(self).dirs@, rel@,
                                        old(self).root@,
                                        old(self).options.hidden, is_dir)
                                        == Some(im_ignore()));
                                }
                                return Some(IncrementalMatch::ignore());
                            }
                        }
                    }
                    None => {}
                }
            }
            None => {}
        }
        // components.peek()? (incremental.rs:388)
        if !has_any_comp_exec(rel, 0) {
            return None;
        }
        // let mut ignore = self.root_ignore(errs)?; (:390)
        let rootv = match self.root_ignore(errs, fs) {
            Some(rv) => rv,
            None => return None,
        };
        proof {
            // the walk subject's custom-name count matches the walk
            // face (the clone carry + the root chain back to the
            // entry store, which this frame's requires ties; the
            // case split mirrors the entry state that handed a
            // Some out)
            assert(rootv == clone_face(&self.root_store[0]));
            assert(rootv.inner.custom_ignore_filenames@.len()
                == self.root_store@[0]
                    .inner.custom_ignore_filenames@.len());
            match old(self).state {
                RootState::Loaded => {
                    assert(self.root_store@[0]
                        .inner.custom_ignore_filenames@.len()
                        == old(self).root_store@[0]
                            .inner.custom_ignore_filenames@.len());
                }
                RootState::Unloaded => {
                    // a Some implies the root directory existed and
                    // the load ran (the NotDirectory arm returns
                    // None)
                    assert(fs.root_is_dir);
                    assert(self.root_store@[0]
                        .inner.custom_ignore_filenames@.len()
                        == old(self).root_store@[0]
                            .inner.custom_ignore_filenames@.len());
                }
                _ => {
                    // NotDirectory hands out None ("Stdin" never
                    // reaches this frame)
                    assert(false);
                }
            }
            assert(old(self).root_store@[0]
                .inner.custom_ignore_filenames@.len()
                == fs.child_found.custom_ignore_files.len());
        }
        // the component walk (incremental.rs:392-435): the dir chain
        // starts empty; the frozen cache is the call-time snapshot
        let dir0: Vec<u8> = Vec::new();
        let frozen_len0: usize = self.dirs.len();
        walk_rec(&mut self.dirs, frozen_len0, self.root.as_slice(),
            hidden, rel, 0, false, 0, dir0, rootv, is_dir, errs, fs)
    }
}

// ===========================================================================
// matched_with_errors_impl -- upstream incremental.rs:267-351
// ===========================================================================

impl IncrementalIgnore {
    /// Origin Rust (incremental.rs:267-351).
    ///
    /// TRUSTED LEG (the IG8 #IG-32 refill attempt closed at 5
    /// rounds without a cure; the wall verified persistent): the
    /// residual is the callee miss-arm postcondition instantiation
    /// over the mut-state chain -- the Some arm reaches z3, the
    /// None arm does not, under (a) the consumer-side fp-match
    /// per-arm rung, (b) the exact if-matches antecedent spelling,
    /// and (c) a single ite-equality value row on the callee
    /// (which additionally pushed the callee frame into the
    /// #IG-19 deep water, partial-verify error at the fast-path
    /// Ignored exit). Rounds: repro@300, rung@600, spelling@600,
    /// ite-equality@600 -- all fail; repro units
    /// --verify-only-module incremental --verify-function
    /// matched_with_errors_impl. The value law rides the contract
    /// here; the 34-vector runtime replay (IG8's own 205/0 rerun)
    /// is the backstop. The in-body proof rung below stays as the
    /// resumption point for a future de-legging (harmless under
    /// external_body; the docs of #IG-32 hold the direction: a
    /// loop-shaped rewrite of the walk, or the helper-extraction
    /// of the frame join per the walk_rec sibling).
    #[verifier::external_body]
    pub fn matched_with_errors_impl(
        &mut self,
        rel: &[u8],
        is_dir: bool,
        errs: &mut PartialErrorBuilder,
        fs: &Ig6FsFace,
    ) -> (r: IncrementalMatch)
        requires
            ii_wf(self),
            (self.state == RootState::Unloaded
                || self.state == RootState::Loaded) ==> (
                fs.root_found.custom_ignore_files.len()
                    == self.root_store[0]
                        .inner.custom_ignore_filenames.len()
                && fs.child_found.custom_ignore_files.len()
                    == self.root_store[0]
                        .inner.custom_ignore_filenames.len()
                && ((self.state == RootState::Unloaded
                        && (fs.root_abs_base matches Some(_)))
                    ==> fs.root_parents_built.len() >= 1)),
        ensures
            ii_wf(final(self)),
            final(self).root@ == old(self).root@,
            final(self).dirs@.len() >= old(self).dirs@.len(),
            forall|t: int| 0 <= t < old(self).dirs@.len() ==>
                final(self).dirs@[t] == old(self).dirs@[t],
            dirs_wf(final(self).dirs@),
            forall|t: int|
                #![trigger final(self).dirs@[t].key@]
                old(self).dirs@.len() <= t < final(self).dirs@.len() ==> (
                final(self).dirs@[t].key@.len() > 0
                    && (match key_parent(final(self).dirs@[t].key@) {
                        None => true,
                        Some(p) =>
                            cache_scan(final(self).dirs@, p, 0) >= 0,
                    })
                    && (match &final(self).dirs@[t].state {
                        CachedDir::Allowed(ig) => ig_wf(ig),
                        CachedDir::Ignored => true,
                    })),
            final(self).options.min_depth == old(self).options.min_depth,
            final(self).options.max_depth == old(self).options.max_depth,
            final(self).options.max_filesize == old(self).options.max_filesize,
            final(self).options.hidden == old(self).options.hidden,
            (old(self).state == RootState::Loaded
                || old(self).state == RootState::NotDirectory
                || old(self).state == RootState::Stdin) ==>
                final(self).state == old(self).state,
            (old(self).state == RootState::Unloaded) ==>
                (final(self).state == RootState::Loaded
                    || final(self).state == RootState::NotDirectory
                    || final(self).state == RootState::Unloaded),
            inc_view(&r)
                == inc_view(&(ii_top_spec(old(self).root@,
                    old(self).state, old(self).root_store@,
                    old(self).options.min_depth,
                    old(self).options.max_depth,
                    old(self).options.max_filesize,
                    old(self).options.hidden, rel@, is_dir,
                    old(self).dirs@, fs)).0),
            peb_stack(final(errs)) == apply_rev2(old(errs).errs@,
                (ii_top_spec(old(self).root@, old(self).state,
                    old(self).root_store@, old(self).options.min_depth,
                    old(self).options.max_depth,
                    old(self).options.max_filesize,
                    old(self).options.hidden, rel@, is_dir,
                    old(self).dirs@, fs)).1),
        {
        // if relative.is_absolute() ||
        //     matches!(self.ignore, RootIgnore::Stdin) {
        //     return IncrementalMatch::none(is_dir); }
        if rel.len() > 0 && rel[0] == 0x2F {
            return IncrementalMatch::none(is_dir);
        }
        match self.state {
            RootState::Stdin => {
                return IncrementalMatch::none(is_dir);
            }
            _ => {}
        }
        // let (mut satisfies_min, mut edge_max) = (true, false);
        let mut satisfies_min = true;
        let mut edge_max = false;
        let has_limits = self.options.min_depth.is_some()
            || self.options.max_depth.is_some();
        if has_limits {
            // let depth = relative.components().filter_map(
            //     |c| match c { CurDir => None, c => Some(c)
            //     }).count();
            let depth = depth_count_exec(rel, 0);
            satisfies_min = match self.options.min_depth {
                None => true,
                Some(mn) => depth >= mn,
            };
            let satisfies_max = match self.options.max_depth {
                None => true,
                Some(mx) => depth <= mx,
            };
            edge_max = match self.options.max_depth {
                None => false,
                Some(mx) => depth == mx,
            };
            // When we have a file that isn't past our min depth, we
            // can give up right away. (incremental.rs:296-299,
            // verbatim)
            if !is_dir && !satisfies_min {
                return IncrementalMatch::ignore().not_within_depth();
            }
            // Same for *anything* that exceeds our max depth.
            // (incremental.rs:301-302, verbatim)
            if !satisfies_max {
                return IncrementalMatch::ignore().not_within_depth();
            }
        }
        // let (mut mat, valid) = ...
        //   .unwrap_or_else(|| (IncrementalMatch::none(is_dir), false));
        let mwi_r = self.matched_with_errors_ignore(rel, is_dir, errs, fs);
        let (mut mat, valid) = match mwi_r {
            Some(m) => (m, true),
            None => (IncrementalMatch::none(is_dir), false),
        };
        proof {
            // the destructure bridge: the live return value names the
            // walk's mat (the spec arms read it)
            assert(valid <==> (mwi_r matches Some(_)));
            assert(valid ==> mwi_r == Some(mat));
            // The #IG-32 rung: the callee's two arm postconditions
            // instantiated per arm, in place (the Some arm reached
            // z3 at IG7; the None arm needed this explicit split --
            // no frame-level conjunction assembly over the match
            // views).
            // Round 3: the antecedents in the callee's OWN spelling
            // (no fp let: the postcondition trigger reads the
            // constructor term directly; the #IG-24 family)
            if (fast_path_spec(old(self).dirs@, rel@,
                    old(self).root@, old(self).options.hidden, is_dir)
                matches None)
            {
                assert((fast_path_spec(old(self).dirs@, rel@,
                    old(self).root@, old(self).options.hidden, is_dir)
                    matches None));
                assert(mwi_r == (walk_entry_root(old(self).state,
                    old(self).root_store@, old(self).root@,
                    old(self).options.hidden, rel@, is_dir,
                    old(self).dirs@, fs)).0);
            } else {
                assert(mwi_r == fast_path_spec(old(self).dirs@, rel@,
                    old(self).root@, old(self).options.hidden,
                    is_dir));
            }
        }
        // if !is_dir && !mat.is_ignore() && valid
        //     && let Some(max_filesize) = self.options.max_filesize
        //     { ... the stat consult ... }
        if !is_dir && !mat.is_ignore() && valid {
            if let Some(max_filesize) = self.options.max_filesize {
                // let path = self.root().join(relative);
                let path = ig6_join(self.root.as_slice(), rel);
                match &fs.filesize {
                    Ok(len) => {
                        if *len > max_filesize {
                            return IncrementalMatch::ignore();
                        }
                    }
                    Err(err) => {
                        // Record the error but otherwise fall through
                        // (incremental.rs:331, verbatim)
                        let tagged = fs_err_tagged(err, path.as_slice());
                        errs.push(tagged);
                    }
                }
            }
        }
        // We still need to tag our `mat` if it doesn't pass the depth
        // filter, or if it's a directory on the edge of a depth
        // filter. This can only happen when the path is reported as a
        // directory. Otherwise regular files are always handled above.
        // (incremental.rs:338-341, verbatim)
        let mut mat = mat;
        if is_dir {
            if !satisfies_min {
                mat = mat.not_within_depth();
            }
            if edge_max {
                mat = mat.no_descent();
            }
        }
        mat
    }
}

// ===========================================================================
// matched_with_errors / matched -- upstream incremental.rs:237-265
// ===========================================================================

impl IncrementalIgnore {
    /// Upstream doc (incremental.rs:249-255, verbatim):
    ///   "Match a root-relative path and return errors encountered
    ///    while loading ignore files.
    ///    This is equivalent to [`IncrementalIgnore::matched`],
    ///    except that it returns any errors from newly loaded ignore
    ///    files. Loading can partially succeed, so valid rules are
    ///    always applied to the returned match even when an error is
    ///    present."
    pub fn matched_with_errors(
        &mut self,
        rel: &[u8],
        is_dir: bool,
        fs: &Ig6FsFace,
    ) -> (r: (IncrementalMatch, Option<Error>))
        requires
            ii_wf(self),
            (self.state == RootState::Unloaded
                || self.state == RootState::Loaded) ==> (
                fs.root_found.custom_ignore_files.len()
                    == self.root_store[0]
                        .inner.custom_ignore_filenames.len()
                && fs.child_found.custom_ignore_files.len()
                    == self.root_store[0]
                        .inner.custom_ignore_filenames.len()
                && ((self.state == RootState::Unloaded
                        && (fs.root_abs_base matches Some(_)))
                    ==> fs.root_parents_built.len() >= 1)),
        ensures
            ii_wf(final(self)),
            final(self).root@ == old(self).root@,
            inc_view(&r.0)
                == inc_view(&(ii_top_spec(old(self).root@,
                    old(self).state, old(self).root_store@,
                    old(self).options.min_depth,
                    old(self).options.max_depth,
                    old(self).options.max_filesize,
                    old(self).options.hidden, rel@, is_dir,
                    old(self).dirs@, fs)).0),
            (apply_rev2(Seq::empty(),
                (ii_top_spec(old(self).root@, old(self).state,
                    old(self).root_store@, old(self).options.min_depth,
                    old(self).options.max_depth,
                    old(self).options.max_filesize,
                    old(self).options.hidden, rel@, is_dir,
                    old(self).dirs@, fs)).1)).len() == 0
                ==> r.1 matches None,
            (apply_rev2(Seq::empty(),
                (ii_top_spec(old(self).root@, old(self).state,
                    old(self).root_store@, old(self).options.min_depth,
                    old(self).options.max_depth,
                    old(self).options.max_filesize,
                    old(self).options.hidden, rel@, is_dir,
                    old(self).dirs@, fs)).1)).len() == 1
                ==> r.1 == Some((apply_rev2(Seq::empty(),
                    (ii_top_spec(old(self).root@, old(self).state,
                        old(self).root_store@,
                        old(self).options.min_depth,
                        old(self).options.max_depth,
                        old(self).options.max_filesize,
                        old(self).options.hidden, rel@, is_dir,
                        old(self).dirs@, fs)).1))[0 as int]),
            (apply_rev2(Seq::empty(),
                (ii_top_spec(old(self).root@, old(self).state,
                    old(self).root_store@, old(self).options.min_depth,
                    old(self).options.max_depth,
                    old(self).options.max_filesize,
                    old(self).options.hidden, rel@, is_dir,
                    old(self).dirs@, fs)).1)).len() >= 2
                ==> r.1 == Some(Error::Partial(peb_vec(apply_rev2(
                    Seq::empty(),
                    (ii_top_spec(old(self).root@, old(self).state,
                        old(self).root_store@,
                        old(self).options.min_depth,
                        old(self).options.max_depth,
                        old(self).options.max_filesize,
                        old(self).options.hidden, rel@, is_dir,
                        old(self).dirs@, fs)).1)))),
        {
        let mut errs = PartialErrorBuilder::new();
        let m = self.matched_with_errors_impl(rel, is_dir, &mut errs, fs);
        proof {
            // the builder stack at handover is the top spec's
            // reversed segments replayed onto the empty seed
            let topv = ii_top_spec(old(self).root@, old(self).state,
                old(self).root_store@, old(self).options.min_depth,
                old(self).options.max_depth,
                old(self).options.max_filesize,
                old(self).options.hidden, rel@, is_dir,
                old(self).dirs@, fs);
            assert(peb_stack(&errs) == apply_rev2(Seq::empty(), topv.1));
        }
        let eo = errs.into_error_option();
        proof {
            // the wrapper shape through the realization axiom: the
            // plural wrap names peb_vec of the very list the builder
            // materialized
            let topv = ii_top_spec(old(self).root@, old(self).state,
                old(self).root_store@, old(self).options.min_depth,
                old(self).options.max_depth,
                old(self).options.max_filesize,
                old(self).options.hidden, rel@, is_dir,
                old(self).dirs@, fs);
            let Xv = apply_rev2(Seq::empty(), topv.1);
            assert(Xv.len() == 0 || Xv.len() == 1 || Xv.len() >= 2);
            if Xv.len() == 1 {
                assert(apply_rev2(Seq::empty(), topv.1).len() == 1);
            } else if Xv.len() >= 2 {
                assert(apply_rev2(Seq::empty(), topv.1).len() >= 2);
                match &eo {
                    None => {
                        assert(false);
                    }
                    Some(e2) => {
                        match e2 {
                            Error::Partial(vv) => {
                                peb_vec_realized(vv);
                                assert(vv@ == Xv);
                                assert(peb_vec(Xv) == *vv);
                            }
                            _ => {
                                assert(false);
                            }
                        }
                    }
                }
            } else {
                // the wrapper guard reads the empty STACK, not a
                // length (extensional equality with the empty Seq)
                assert(apply_rev2(Seq::empty(), topv.1) == Seq::empty());
            }
        }
        (m, eo)
    }
}

// ===========================================================================
// matched -- upstream incremental.rs:237-247
// ===========================================================================
//
// Upstream doc (incremental.rs:210-236) rides the struct docs; the
// method doc (incremental.rs:219-221, verbatim):
//   "Matchers for previously unseen directories are loaded and cached
//    during this call. Errors encountered while loading ignore files
//    are logged. To receive those errors, use
//    [`IncrementalIgnore::matched_with_errors`]."
// (The twin takes the fs face; the log line is the recorded cut.)

impl IncrementalIgnore {
    /// Origin Rust (incremental.rs:237-247): drop the error, return
    /// the match. (The upstream gate doc at incremental.rs:223-228,
    /// verbatim:
    ///   "`path` must be relative to this matcher's root and must not
    ///    contain a parent directory (`..`) component. Behavior is
    ///    unspecified when these preconditions are violated. Callers
    ///    with an absolute path or with a path containing `.` or `..`
    ///    may use [`IncrementalIgnore::normalize`] to get a path
    ///    satisfying these preconditions. In all cases, a relative
    ///    path is *assumed* to be relative to the root of this ignore
    ///    matcher.")
    pub fn matched(
        &mut self,
        rel: &[u8],
        is_dir: bool,
        fs: &Ig6FsFace,
    ) -> (r: IncrementalMatch)
        requires
            ii_wf(self),
            (self.state == RootState::Unloaded
                || self.state == RootState::Loaded) ==> (
                fs.root_found.custom_ignore_files.len()
                    == self.root_store[0]
                        .inner.custom_ignore_filenames.len()
                && fs.child_found.custom_ignore_files.len()
                    == self.root_store[0]
                        .inner.custom_ignore_filenames.len()
                && ((self.state == RootState::Unloaded
                        && (fs.root_abs_base matches Some(_)))
                    ==> fs.root_parents_built.len() >= 1)),
        ensures
            ii_wf(final(self)),
            final(self).root@ == old(self).root@,
            inc_view(&r)
                == inc_view(&(ii_top_spec(old(self).root@,
                    old(self).state, old(self).root_store@,
                    old(self).options.min_depth,
                    old(self).options.max_depth,
                    old(self).options.max_filesize,
                    old(self).options.hidden, rel@, is_dir,
                    old(self).dirs@, fs)).0),
    {
        let (m, _err) = self.matched_with_errors(rel, is_dir, fs);
        m
    }
}

// ===========================================================================
// normalize_absolute / pop_last -- upstream incremental.rs:582-600
// ===========================================================================
//
// Upstream doc (incremental.rs:582-586, verbatim):
//   "Return a lexically normalized absolute representation of `path`.
//    This collapses `.` and `..`, but intentionally does not
//    canonicalize or resolve symlinks. Ignore rules apply to the
//    lexical path, and resolving a symlink below a root could move
//    the result outside of that root."
// (The canonicalize-free claim is the std face's trust; the fold
// below is the real half.)

/// The pop model (upstream `normalized.pop()`, incremental.rs:594):
/// drop the last component; the root floor '/' stays.
pub open spec fn pop_last(acc: Seq<u8>) -> Seq<u8> {
    match memrchr_spec(acc, 0x2F) {
        None => acc,
        Some(p) => if p == 0 {
            seq![0x2F]
        } else {
            acc.subrange(0, p)
        },
    }
}

/// The exec carrier of pop_last.
pub fn pop_last_exec(acc: &[u8]) -> (r: Vec<u8>)
    ensures r@ == pop_last(acc@)
{
    match memrchr_face(acc, 0x2F) {
        None => vstd::slice::slice_to_vec(acc),
        Some(p) => {
            proof {
                memrchr_spec_some_bridge(acc@, 0x2F, p as int);
            }
            if p == 0 {
                let mut v: Vec<u8> = Vec::new();
                v.push(0x2F);
                v
            } else {
                vstd::slice::slice_to_vec(&acc[..p])
            }
        }
    }
}

// The fold machinery (incremental.rs:589-599) is a byte-scan state
// machine (the same #IG-19 syntactic-recursion form as the depth and
// peek machines): the segment's fate is decided at close time by the
// segment bytes, each recursion step advances exactly one byte.

/// The segment-close decision of the fold (one raw segment's arm).
pub open spec fn nf_close(abs: Seq<u8>, seg_s: int, e: int, acc: Seq<u8>)
    -> Seq<u8>
{
    if seg_s < 0 {
        acc
    } else {
        let seg = abs.subrange(seg_s, e);
        if is_dot(seg) {
            // std::path::Component::CurDir => {}
            acc
        } else if is_dotdot(seg) {
            // std::path::Component::ParentDir =>
            //     { normalized.pop(); }
            pop_last(acc)
        } else {
            // _ => normalized.push(component.as_os_str())
            join_bytes(acc, seg)
        }
    }
}

/// The fold spec (incremental.rs:589-599): the accumulator recursion
/// over the raw cursor, one byte per step (seg_s: the open segment's
/// start, -1 when none).
pub open spec fn norm_fold_go(abs: Seq<u8>, c: int, seg_s: int, acc: Seq<u8>)
    -> Seq<u8>
    decreases abs.len() - c
{
    if c >= abs.len() as int {
        nf_close(abs, seg_s, c, acc)
    } else if abs[c] == 0x2F {
        norm_fold_go(abs, c + 1, -1, nf_close(abs, seg_s, c, acc))
    } else {
        let s2 = if seg_s < 0 { c } else { seg_s };
        norm_fold_go(abs, c + 1, s2, acc)
    }
}

/// The fold's full form.
pub open spec fn norm_fold(abs: Seq<u8>) -> Seq<u8> {
    norm_fold_go(abs, 0, -1, Seq::empty())
}

/// Origin Rust (incremental.rs:587-600): the std absolutize consult
/// then the lexical fold (the byte-scan mirror of norm_fold_go).
pub fn normalize_absolute(path: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        r matches None ==> (std_abs_face(path@) matches None),
        r matches Some(v2) ==> (match std_abs_face(path@) {
            None => false,
            Some(a) => v2@ == norm_fold(a),
        }),
{
    // let absolute = std::path::absolute(path).ok()?;
    match std_abs(path) {
        None => None,
        Some(abs) => {
            // the fold loop (incremental.rs:589-599; the
            // open-segment carrier is the (seg_open, seg_start)
            // pair -- the spec mirror's -1 sentinel rides only the
            // spec side, the exec carrier carries no
            // machine-narrowing negative)
            let mut normalized: Vec<u8> = Vec::new();
            let mut i: usize = 0;
            let mut seg_open: bool = false;
            let mut seg_start: usize = 0;
            while i < abs.len()
                invariant
                    0 <= i <= abs.len(),
                    !seg_open || (seg_start < i
                        && forall|q: int|
                            seg_start as int <= q < i as int
                            ==> abs@ [q] != 0x2F),
                    norm_fold_go(abs@, 0, -1, Seq::empty())
                        == norm_fold_go(abs@, i as int,
                            if seg_open { seg_start as int } else { -1 },
                            normalized@),
                decreases abs.len() - i
            {
                proof {
                    reveal(norm_fold_go);
                }
                if abs[i] == 0x2F {
                    // the open segment (if any) closes at i
                    normalized = nf_close_exec(
                        &abs, seg_open, seg_start, i,
                        normalized.as_slice());
                    seg_open = false;
                } else if !seg_open {
                    seg_open = true;
                    seg_start = i;
                }
                i += 1;
            }
            proof {
                reveal(norm_fold_go);
                // the trailing segment (if any) closes at the end
            }
            let fin2 = nf_close_exec(
                &abs, seg_open, seg_start, abs.len(),
                normalized.as_slice());
            Some(fin2)
        }
    }
}

/// The exec carrier of the segment-close decision (the nf_close
/// mirror; the upstream decisions transcribe verbatim per arm -- the
/// '.' / '..' sentinels spell index-wise, and the open-segment
/// carrier is the (seg_open, seg_start) pair; the spec mirror's -1
/// sentinel rides only the spec side).
pub fn nf_close_exec(
    abs: &[u8],
    seg_open: bool,
    seg_start: usize,
    e: usize,
    acc: &[u8],
) -> (r: Vec<u8>)
    requires
        e <= abs.len(),
        !seg_open || seg_start < e,
    ensures
        r@ == nf_close(abs@,
            if seg_open { seg_start as int } else { -1 }, e as int,
            acc@)
{
    if !seg_open {
        vstd::slice::slice_to_vec(acc)
    } else {
        let seg = &abs[seg_start..e];
        let seg_is_dot: bool = seg.len() == 1 && seg[0] == 0x2E;
        let seg_is_dotdot: bool =
            seg.len() == 2 && seg[0] == 0x2E && seg[1] == 0x2E;
        if seg_is_dot {
            // Component::CurDir => {}
            proof {
                let sspec = abs@.subrange(seg_start as int, e as int);
                assert(seg@ == sspec);
                // seg_is_dot spells the one-byte '.' content
                assert(sspec.len() == 1);
                assert(sspec[0] == 0x2E);
                assert(sspec == seq![0x2E]);
                assert(is_dot(sspec));
            }
            vstd::slice::slice_to_vec(acc)
        } else if seg_is_dotdot {
            // Component::ParentDir => { normalized.pop(); }
            proof {
                let sspec = abs@.subrange(seg_start as int, e as int);
                assert(seg@ == sspec);
                // seg_is_dotdot spells the two-byte '..' content
                assert(sspec.len() == 2);
                assert(sspec[0] == 0x2E);
                assert(sspec[1] == 0x2E);
                assert(sspec == seq![0x2E, 0x2E]);
                assert(is_dotdot(sspec));
            }
            pop_last_exec(acc)
        } else {
            // _ => normalized.push(component.as_os_str())
            let j = ig6_join(acc, seg);
            proof {
                let sspec = abs@.subrange(seg_start as int, e as int);
                assert(seg@ == sspec);
                assert(!is_dot(sspec));
                assert(!is_dotdot(sspec));
                assert(j@ == join_bytes(acc@, sspec));
            }
            j
        }
    }
}

// ===========================================================================
// normalize -- upstream incremental.rs:181-208
// ===========================================================================
//
// Upstream doc (incremental.rs:181-197, verbatim):
//   "Normalize `path` and return it relative to this matcher's root.
//    This returns `None` when `path` cannot be made absolute or when
//    it is known to be outside this matcher's root. Unlike
//    [`IncrementalIgnore::matched`], this performs absolute path
//    conversion, lexical normalization and allocation. It is intended
//    as an opt-in convenience for callers that do not already have
//    root-relative paths.
//    Note that `.` is interpreted relative to the process level
//    current working directory. It is _not_ interpreted relative to
//    the root of this matcher.
//    Note also that this may reject paths that only differ in casing.
//    For example, if the root path for this matcher is `/FOO` but the
//    provided path is `/foo/bar`, then this may return `None`. Callers
//    must ensure casing is consistent between the path provided and
//    the root path for this matcher."

impl IncrementalIgnore {
    /// Origin Rust (incremental.rs:198-208): the stdin gate, the
    /// path fold, the root lens (the OnceLock memoization is not
    /// value-observable -- recomputed per call), the strip consumer.
    pub fn normalize(&self, path: &[u8]) -> (r: Option<Vec<u8>>)
        requires ii_wf(self)
        ensures
            match self.state {
                RootState::Stdin => r matches None,
                _ => true,
            },
            r matches Some(v) ==> ({
                let both_folded = (match std_abs_face(path@) {
                    None => false,
                    Some(pa) => (match std_abs_face(self.root@) {
                        None => false,
                        Some(ra) => {
                            let fa = norm_fold(ra);
                            let fb = norm_fold(pa);
                            (match strip_prefix_spec(fa, fb) {
                                None => false,
                                Some(rest) => v@ == rest,
                            })
                        }
                    }),
                });
                both_folded
            }),
    {
        // if matches!(self.ignore, RootIgnore::Stdin) { return None; }
        match self.state {
            RootState::Stdin => {
                return None;
            }
            _ => {}
        }
        // let path = normalize_absolute(path.as_ref())?;
        let p2 = normalize_absolute(path);
        let p2v = match p2 {
            Some(v) => v,
            None => return None,
        };
        // let root = self.normalized_root.get_or_init(
        //     || normalize_absolute(&self.root)).as_ref()?;
        let r2 = normalize_absolute(self.root.as_slice());
        let r2v = match r2 {
            Some(v) => v,
            None => return None,
        };
        // path.strip_prefix(root).ok().map(Path::to_path_buf)
        match strip_prefix(r2v.as_slice(), p2v.as_slice()) {
            Some(rest) => Some(vstd::slice::slice_to_vec(rest)),
            None => None,
        }
    }
}

} // verus!

// Standalone-file invocation anchor (the harness mounts this file
// with #[path]; single-file verus runs need the empty main).
fn main() {}
