//! ignore 0.4.34 (pin `178cc027`) -- Verus transcription of upstream
//! `crates/ignore/src/overrides.rs`, batch IG4.
//!
//! Upstream module doc (overrides.rs:1-6, verbatim):
//!   "The overrides module provides a way to specify a set of override
//!    globs.
//!    This provides functionality similar to `--include` or `--exclude`
//!    in command line tools."
//!
//! Scope (inventory section 10, batch IG4): the full file -- the
//! `Override` wrapper over `Gitignore` (empty / path / is_empty /
//! DP18's mirrored counts / the invert + unmatched-ignore fallback of
//! `matched`, DP19), and `OverrideBuilder`. The match machinery
//! underneath (strip, the highest-precedent scan, the `!`-semantics
//! rewrite chain of `GitignoreBuilder::add_line`) is the IG2/IG3 twin
//! consumed AS IS -- every spec term below is spelled out of the
//! gitignore twin's public spec family (gi_decide, gi_decide_view,
//! globs_field_view, gi_strip_spec), per the IG3 handoff notes.
//!
//! Modeling declarations (Origin: every deviation recorded):
//! - **Borrow-chain face.** Upstream `Glob<'a>(GlobInner<'a>)`
//!   wraps `&'a gitignore::Glob`; the twin wraps an owned
//!   `super::gitignore::Glob` (the GI3 convention: `matched` returns
//!   owned payload copies; `copy_glob`'s field-preserving post makes
//!   the two observationally equal at the view tier).
//! - **`Match::map` inlining.** Upstream `matched` closes with
//!   `mat.map(move |giglob| Glob(GlobInner::Matched(giglob)))`; the
//!   twin spells the three match arms out (the lib twin's exec
//!   `Match::map` is shape-only -- `call_requires` face -- so the
//!   value law is carried by the arms; cf. lib.rs `Match::map`).
//! - **Chainable `&mut Self` returns** of `add`/`case_insensitive`
//!   collapse to `Result<(), Error>` (the IG2/IG3 `add_line`
//!   precedent).
//! - Upstream `#[derive(Clone, Debug)]` on both structs: the Clone/Debug
//!   tier is outside the verified surface (noted, gitignore twin same).

use vstd::prelude::*;
use vstd::seq::Seq;

use super::gitignore::{
    self, gi_decide, gi_decide_view, gi_match_view, gi_strip_spec, globs_field_view,
    Gitignore, GitignoreBuilder,
};
use super::Error;
use super::Match;

verus! {

// ===========================================================================
// Glob -- upstream overrides.rs:15-43
// ===========================================================================

/// Upstream doc (overrides.rs:16-25, verbatim):
///   "Glob represents a single glob in an override matcher.
///    This is used to report information about the highest precedent
///    glob that matched.
///    Note that not all matches necessarily correspond to a specific
///    glob. For example, if there are one or more whitelist globs and
///    a file path doesn't match any glob in the set, then the file
///    path is considered to be ignored.
///    The lifetime `a` refers to the lifetime of the matcher that
///    produced this glob."
#[allow(dead_code)]
pub struct Glob(
    /// (opened pub: the open spec fns below pattern the wrapper)
    pub GlobInner,
);

/// (Upstream this enum is private; the twin opens it pub for the
/// mount-visibility convention -- ov_match_view, an open spec fn the
/// harness rows consume, patterns the variants.)
#[allow(dead_code)]
pub enum GlobInner {
    /// No glob matched, but the file path should still be ignored.
    UnmatchedIgnore,
    /// A glob matched (the wrapped gitignore twin's Glob).
    Matched(super::gitignore::Glob),
}

// ===========================================================================
// Override -- upstream overrides.rs:45-111
// ===========================================================================

/// Upstream doc (overrides.rs:45-47, verbatim): "Manages a set of
/// overrides provided explicitly by the end user." (upstream
/// `pub struct Override(Gitignore)` -- the newtype is kept verbatim;
/// pub field below only for the harness `#[path]` mounts, the
/// mount-visibility convention crate-wide).
pub struct Override {
    /// The wrapped gitignore matcher (upstream private tuple field).
    pub inner: Gitignore,
}

/// The view of one override `Match` verdict: outer `Some` iff not
/// `Match::None`; the bool is whitelist(=non-'!'-globs at the override
/// tier)/ignore at the OVERRIDE tier; the payload option is
/// `None` for `Glob::unmatched()` and the matched glob's field view
/// otherwise (the same five-field view the gitignore rows use).
pub open spec fn ov_match_view(
    m: Match<Glob>,
) -> Option<(bool, Option<(Seq<u8>, Seq<u8>, bool, bool, Option<Seq<u8>>)>)>

{
    match m {
        Match::None => None,
        Match::Whitelist(Glob(GlobInner::Matched(g))) =>
            Some((true, Some(globs_field_view(g)))),
        Match::Ignore(Glob(GlobInner::Matched(g))) =>
            Some((false, Some(globs_field_view(g)))),
        Match::Ignore(Glob(GlobInner::UnmatchedIgnore)) => Some((false, None)),
        Match::Whitelist(Glob(GlobInner::UnmatchedIgnore)) => Some((true, None)),
    }
}

/// The spec track of `Override::matched` (overrides.rs:97-110). The
/// face terms: `gi_decide` over the gitignore twin's stores, the
/// strip view `gi_strip_spec`, and the two wrapper specials -- the
/// whitelist inversion (`!wl`) and DP19's unmatched-ignore fallback
/// (the fallback condition `self.num_whitelists() > 0` is, by the
/// DP18 mirror, the wrapped matcher's `num_ignores` -- the count of
/// NON-'!' lines, which ARE the override tier's whitelist globs).
pub open spec fn ov_matched_spec(
    o: &Override,
    path: Seq<u8>,
    is_dir: bool,
) -> Option<(bool, Option<(Seq<u8>, Seq<u8>, bool, bool, Option<Seq<u8>>)>)>
{
    if o.inner.set.registered@.len() == 0 {
        // `if self.is_empty() { return Match::None; }` (overrides.rs:102)
        None
    } else {
        match gi_decide(
            o.inner.globs@,
            o.inner.set.registered@,
            gi_strip_spec(o.inner.root.bytes@, path),
            is_dir,
        ) {
            None => {
                if (o.inner.num_ignores > 0 && !is_dir) {
                    // `if mat.is_none() && self.num_whitelists() > 0
                    //  && !is_dir` (overrides.rs:106) -- the
                    //  num_whitelists mirror is o.inner.num_ignores.
                    Some((false, None))
                } else {
                    None
                }
            }
            Some((wl, i)) =>
                Some((!wl, Some(globs_field_view(o.inner.globs@[i])))),
        }
    }
}

impl Override {
    /// Upstream doc (overrides.rs:50, verbatim):
    ///   "Returns an empty matcher that never matches any file path."
    pub fn empty() -> (r: Override)
        ensures
            r.inner.set.registered@.len() == 0,
            r.inner.root.bytes@.len() == 0,
            r.inner.globs@.len() == 0,
            r.inner.num_ignores == 0,
            r.inner.num_whitelists == 0,
    {
        // Overrides(Gitignore::empty()) (overrides.rs:52)
        Override { inner: Gitignore::empty() }
    }

    /// Upstream doc (overrides.rs:55-57, verbatim):
    ///   "Returns the directory of this override set.
    ///    All matches are done relative to this path."
    pub fn path(&self) -> (r: &[u8])
        ensures r@ == self.inner.root.bytes@
    {
        self.inner.path()
    }

    /// Upstream doc (overrides.rs:63-65, verbatim):
    ///   "Returns true if and only if this matcher is empty.
    ///    When a matcher is empty, it will never match any file path."
    pub fn is_empty(&self) -> (r: bool)
        ensures r == (self.inner.set.registered@.len() == 0)
    {
        self.inner.is_empty()
    }

    /// Upstream doc (overrides.rs:69, verbatim):
    ///   "Returns the total number of ignore globs."
    /// (DP18, overrides.rs:70-72: the body is `self.0.num_whitelists()`
    /// -- the NAME-SWAPPED mirror of the inverted `!` semantics.
    /// Read at the override tier the doc is correct: the `!`-prefixed
    /// globs are the ignore ones, and in the wrapped gitignore those
    /// are the whitelist records. Cross-noted, not a finding; the
    /// runtime S13 DP18 columns pin the values both ways.)
    pub fn num_ignores(&self) -> (r: u64)
        ensures r == self.inner.num_whitelists
    {
        // self.0.num_whitelists() (overrides.rs:71)
        self.inner.num_whitelists()
    }

    /// Upstream doc (overrides.rs:74, verbatim):
    ///   "Returns the total number of whitelisted globs."
    /// (DP18 mirror twin of `num_ignores`: the body is
    /// `self.0.num_ignores()` -- the wrapped matcher's plain globs,
    /// which are '!'-free and therefore whitelist globs at the
    /// override tier.)
    pub fn num_whitelists(&self) -> (r: u64)
        ensures r == self.inner.num_ignores
    {
        // self.0.num_ignores() (overrides.rs:76)
        self.inner.num_ignores()
    }

    /// Upstream doc (overrides.rs:79-96, verbatim):
    ///   "Returns whether the given file path matched a pattern in this
    ///    override matcher.
    ///    `is_dir` should be true if the path refers to a directory and
    ///    false otherwise.
    ///    If there are no overrides, then this always returns
    ///    `Match::None`.
    ///    If there is at least one whitelist override and `is_dir` is
    ///    false, then this never returns `Match::None`, since
    ///    non-matches are interpreted as ignored.
    ///    The given path is matched to the globs relative to the path
    ///    given when building the override matcher. Specifically,
    ///    before matching `path`, its prefix (as determined by a common
    ///    suffix of the directory given) is stripped. If there is no
    ///    common suffix/prefix overlap, then `path` is assumed to
    ///    reside in the same directory as the root path for this set
    ///    of overrides."
    pub fn matched(&self, path: &[u8], is_dir: bool) -> (r: Match<Glob>)
        ensures ov_match_view(r) == ov_matched_spec(self, path@, is_dir)
    {
        // :102-104 `if self.is_empty() { return Match::None; }`
        if self.is_empty() {
            proof {
                assert(self.inner.set.registered@.len() == 0);
                assert(ov_matched_spec(self, path@, is_dir) matches None);
            }
            return Match::None;
        }
        // :105 `let mat = self.0.matched(path, is_dir).invert();`
        // (fused with the :109 map below: the lib twin's `invert` and
        // `map` are shape-only at the exec tier, so the value law --
        // which payload rides which arm -- is carried by spelling the
        // inversion+wrap per arm; see the header note)
        let m = self.inner.matched(path, is_dir);
        // :106-108 the unmatched-ignore fallback (DP19; the
        // num_whitelists() term is the DP18 mirror: wrapped
        // num_ignores, i.e. the count of '!'-free lines)
        if m.is_none() && self.num_whitelists() > 0 && !is_dir {
            proof {
                reveal(ov_match_view);
                reveal(ov_matched_spec);
                let d = gi_decide(
                    self.inner.globs@,
                    self.inner.set.registered@,
                    gi_strip_spec(self.inner.root.bytes@, path@),
                    is_dir,
                );
                // m is None: its gitignore view is None, so d is None
                assert(gi_decide_view(d, self.inner.globs@) == gi_match_view(m));
                assert(gi_match_view(m) matches None);
                assert(d matches None);
                assert(self.inner.num_ignores > 0);
                assert(ov_matched_spec(self, path@, is_dir) == Some((false, None)));
            }
            return Match::Ignore(Glob(GlobInner::UnmatchedIgnore));
        }
        // inverted+wrapped arms (overrides.rs:105+:109)
        match m {
            Match::None => {
                proof {
                    // the fallback did not fire: no whitelist globs, or a dir
                    assert(self.inner.num_ignores == 0 || is_dir);
                    reveal(ov_match_view);
                    reveal(ov_matched_spec);
                    let d = gi_decide(
                        self.inner.globs@,
                        self.inner.set.registered@,
                        gi_strip_spec(self.inner.root.bytes@, path@),
                        is_dir,
                    );
                    assert(gi_decide_view(d, self.inner.globs@) matches None);
                    assert(d matches None);
                    assert(ov_matched_spec(self, path@, is_dir) matches None);
                }
                Match::None
            }
            Match::Whitelist(g) => {
                // gi-whitelist ('!'-free line) -> override Ignore
                proof {
                    reveal(ov_match_view);
                    reveal(ov_matched_spec);
                    let d = gi_decide(
                        self.inner.globs@,
                        self.inner.set.registered@,
                        gi_strip_spec(self.inner.root.bytes@, path@),
                        is_dir,
                    );
                    assert(gi_decide_view(d, self.inner.globs@)
                        == Some((true, globs_field_view(g))));
                    assert(d matches Some((_, _)));
                    match d {
                        None => {},
                        Some((wl, i)) => {
                            assert(wl);
                            assert(!wl == false);
                            assert(globs_field_view(self.inner.globs@[i])
                                == globs_field_view(g));
                        }
                    }
                    assert(ov_matched_spec(self, path@, is_dir)
                        == Some((false, Some(globs_field_view(g)))));
                }
                Match::Ignore(Glob(GlobInner::Matched(g)))
            }
            Match::Ignore(g) => {
                // gi-ignore ('!'-line) -> override Whitelist
                proof {
                    reveal(ov_match_view);
                    reveal(ov_matched_spec);
                    let d = gi_decide(
                        self.inner.globs@,
                        self.inner.set.registered@,
                        gi_strip_spec(self.inner.root.bytes@, path@),
                        is_dir,
                    );
                    assert(gi_decide_view(d, self.inner.globs@)
                        == Some((false, globs_field_view(g))));
                    assert(d matches Some((_, _)));
                    match d {
                        None => {},
                        Some((wl, i)) => {
                            assert(!wl);
                            assert(globs_field_view(self.inner.globs@[i])
                                == globs_field_view(g));
                        }
                    }
                    assert(ov_matched_spec(self, path@, is_dir)
                        == Some((true, Some(globs_field_view(g)))));
                }
                Match::Whitelist(Glob(GlobInner::Matched(g)))
            }
        }
    }
}

/// DP19 (overrides.rs:85-89: "If there is at least one whitelist
/// override and `is_dir` is false, then this never returns
/// `Match::None`"): the promise at the spec tier -- with at least one
/// whitelist override ('!'-free line, the wrapped matcher's
/// num_ignores > 0) and a non-directory, `ov_matched_spec` is
/// always Some, hence `matched` never returns Match::None on any
/// path (the twin of the upstream promise; runtime S13 DP19 columns).
pub proof fn dp19_never_none(o: &Override, path: Seq<u8>, is_dir: bool)
    requires
        o.inner.set.registered@.len() > 0,
        o.inner.num_ignores > 0,
        !is_dir,
    ensures ov_matched_spec(o, path, is_dir) matches Some(_)
{
}

// ===========================================================================
// OverrideBuilder -- upstream overrides.rs:113-184
// ===========================================================================

/// Upstream doc (overrides.rs:113-115, verbatim):
///   "Builds a matcher for a set of glob overrides."
pub struct OverrideBuilder {
    /// Upstream private field `builder: GitignoreBuilder` (opened pub
    /// for the harness mounts per the crate-wide convention).
    pub builder: GitignoreBuilder,
}

impl OverrideBuilder {
    /// Upstream doc (overrides.rs:119-121, verbatim):
    ///   "Create a new override builder.
    ///    Matching is done relative to the directory path provided."
    /// Body (overrides.rs:122-127): `GitignoreBuilder::new(path)` then
    /// `builder.allow_unclosed_class(false)` -- the DP8 pin: overrides
    /// run the unclosed-class-default-false policy, documented as a
    /// deliberate divergence from Gitignore's default-true
    /// (upstream overrides.rs:175-183; the gitignore twin carries the
    /// cross-note at its allow_unclosed_class).
    pub fn new(root: &[u8]) -> (r: OverrideBuilder)
        ensures
            r.builder.root.bytes@ == super::gitignore::root_strip_view(root@),
            r.builder.globs@.len() == 0,
            r.builder.builder.registered@.len() == 0,
            !r.builder.case_insensitive,
            !r.builder.allow_unclosed_class, // overrides.rs:125
    {
        let mut builder = GitignoreBuilder::new(root);
        builder.allow_unclosed_class(false);
        OverrideBuilder { builder }
    }

    /// Upstream doc (overrides.rs:129-131, verbatim):
    ///   "Builds a new override matcher from the globs added so far.
    ///    Once a matcher is built, no new globs can be added to it."
    /// (`Ok(Override(self.builder.build()?))`, overrides.rs:132-134:
    /// the `?` leg never realizes on the twin face -- the gitignore
    /// twin's build admits the GlobSetBuilder::build leg, so its
    /// result is always Ok; transcribed as the direct wrap, the
    /// dead map_err arm recorded in this comment.)
    pub fn build(&self) -> (r: Result<Override, Error>)
        ensures
            r matches Ok(_),
    {
        let inner = match self.builder.build() {
            Ok(g) => g,
            Err(_) => Gitignore::empty(), // unreachable per the face note
        };
        Ok(Override { inner })
    }

    /// Upstream doc (overrides.rs:136-141, verbatim):
    ///   "Add a glob to the set of overrides.
    ///    Globs provided here have precisely the same semantics as a
    ///    single line in a `gitignore` file, where the meaning of `!`
    ///    is inverted: namely, `!` at the beginning of a glob will
    ///    ignore a file. Without `!`, all matches of the glob provided
    ///    are treated as whitelist matches."
    /// Body (overrides.rs:142-145): `self.builder.add_line(None,
    /// glob)?` -- the contract is the add_line twin's, transplanted
    /// over the `builder` field (from = None: `from_view(None) ==
    /// None`, the pitfall-free arm of the gitignore store spec).
    pub fn add(&mut self, glob: &[u8]) -> (r: Result<(), Error>)
        ensures
            final(self).builder.case_insensitive
                == old(self).builder.case_insensitive,
            final(self).builder.allow_unclosed_class
                == old(self).builder.allow_unclosed_class,
            final(self).builder.root == old(self).builder.root,
            super::gitignore::outcome_skip(
                old(self).builder.case_insensitive,
                old(self).builder.allow_unclosed_class, None, glob@)
                ==> (r matches Ok(_)
                    && final(self).builder.globs@ == old(self).builder.globs@
                    && final(self).builder.builder.registered@
                        == old(self).builder.builder.registered@),
            super::gitignore::outcome_add_ok(
                old(self).builder.case_insensitive,
                old(self).builder.allow_unclosed_class, None, glob@)
                ==> (r matches Ok(_)
                    && final(self).builder.globs@.len()
                        == old(self).builder.globs@.len() + 1
                    && final(self).builder.builder.registered@.len()
                        == old(self).builder.builder.registered@.len() + 1
                    && (forall|k: int| #![trigger
                            globs_field_view(old(self).builder.globs@[k])]
                        0 <= k < old(self).builder.globs@.len() ==>
                        (globs_field_view(final(self).builder.globs@[k])
                            == globs_field_view(old(self).builder.globs@[k])))
                    && (forall|k: int| #![trigger
                            old(self).builder.builder.registered@[k].pattern@]
                        0 <= k < old(self).builder.builder.registered@.len()
                        ==> (final(self).builder.builder.registered@[k].pattern@
                            == old(self).builder.builder.registered@[k].pattern@
                            && final(self).builder.builder.registered@[k]
                                .case_insensitive
                            == old(self).builder.builder.registered@[k]
                                .case_insensitive))),
            super::gitignore::outcome_add_rejected(
                old(self).builder.case_insensitive,
                old(self).builder.allow_unclosed_class, None, glob@)
                ==> (r matches Err(e)
                    && e matches Error::Glob { glob: Some(_), err: _ }
                    && final(self).builder.globs@ == old(self).builder.globs@
                    && final(self).builder.builder.registered@
                        == old(self).builder.builder.registered@),
    {
        // self.builder.add_line(None, glob)? (overrides.rs:143)
        let line = glob;
        self.builder.add_line(None, line)
    }

    /// Upstream doc (overrides.rs:143-152, verbatim):
    ///   "Toggle whether the globs should be matched case
    ///    insensitively or not.
    ///    When this option is changed, only globs added after the
    ///    change will be affected.
    ///    This is disabled by default."
    /// (upstream overrides.rs:153-161 also carries the maintainer
    /// TODO, verbatim: `// TODO: This should not return a `Result`.
    ///  Fix this in the next semver release.` -- kept here as the
    /// historical record; the twin keeps the Result skin either way.)
    pub fn case_insensitive(&mut self, yes: bool) -> (r: Result<(), Error>)
        ensures
            r matches Ok(_),
            final(self).builder.case_insensitive == yes,
            final(self).builder.allow_unclosed_class
                == old(self).builder.allow_unclosed_class,
            final(self).builder.globs@ == old(self).builder.globs@,
            final(self).builder.builder.registered@
                == old(self).builder.builder.registered@,
            final(self).builder.root == old(self).builder.root,
    {
        self.builder.case_insensitive(yes)?;
        Ok(())
    }

    /// Upstream doc (overrides.rs:147-172, verbatim):
    ///   "Toggle whether unclosed character classes are allowed. When
    ///    allowed, a `[` without a matching `]` is treated literally
    ///    instead of resulting in a parse error.
    ///    For example, if this is set then the glob `[abc` will be
    ///    treated as the literal string `[abc` instead of returning an
    ///    error.
    ///    By default, this is false. Generally speaking, enabling this
    ///    leads to worse failure modes since the glob parser becomes
    ///    more permissive. You might want to enable this when
    ///    compatibility (e.g., with POSIX glob implementations) is
    ///    more important than good error messages.
    ///    This default is different from the default for [`Gitignore`].
    ///    Namely, [`Gitignore`] is intended to match git's behavior
    ///    as-is. But this abstraction for 'override' globs does not
    ///    necessarily conform to any other known specification and
    ///    instead prioritizes better error messages."
    /// (This is the doc that pins the DP8 divergence; here it returns
    /// `()` -- the upstream `&mut OverrideBuilder` chain face collapsed
    /// per the header note.)
    pub fn allow_unclosed_class(&mut self, yes: bool) -> ()
        ensures
            final(self).builder.allow_unclosed_class == yes,
            final(self).builder.case_insensitive
                == old(self).builder.case_insensitive,
            final(self).builder.globs@ == old(self).builder.globs@,
            final(self).builder.builder.registered@
                == old(self).builder.builder.registered@,
            final(self).builder.root == old(self).builder.root,
    {
        self.builder.allow_unclosed_class(yes);
    }
}

} // verus!

// Standalone-file invocation anchor (the harness mounts this file with
// #[path]; single-file verus runs need the empty main).
fn main() {}
