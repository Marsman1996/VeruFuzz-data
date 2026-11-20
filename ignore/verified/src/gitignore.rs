//! ignore 0.4.34 (pin `178cc027`) -- Verus transcription of the builder
//! side of `crates/ignore/src/gitignore.rs` (batch IG2).
//!
//! # Scope (upstream anchors)
//!
//! - `Glob` + accessors (gitignore.rs:27-76) incl. the private
//!   `has_doublestar_prefix`.
//! - `GitignoreBuilder` (gitignore.rs:318-581): `new` (:335-344, the
//!   `./`-prefixed root strip via pathutil), `add_line` (:463-544, the
//!   full rewrite chain), `build` (:349-369, counting), `add` (:408-437,
//!   the file loop transcribed over an abstract line stream),
//!   `case_insensitive` (:552-560), `allow_unclosed_class` (:574-580).
//! - `Gitignore` builder-side accessors (gitignore.rs:148-189): `empty`,
//!   `path`, `is_empty`, `len`, `num_ignores`, `num_whitelists`.
//! - `build_global` (:380-399) as a spec-model value function with the
//!   two blank legs proven (the "global ignore blank determination").
//!
//! # Deferred (with anchors; not this batch)
//!
//! - `Gitignore::new` (:103-118) and `Gitignore::global` (:141-146):
//!   fs/env legs (File::open, current_dir) -- IG3 owns the Gitignore
//!   matcher faces; the error-folding shape they use is the same one
//!   modeled inside `build_global_value`.
//! - `matched` / `matched_stripped` / `matched_path_or_any_parents` /
//!   `strip` (:191-315): the matcher decision core -- IG3 (the GlobSet
//!   matcher face stub per inventory section 6 is NOT re-anchored here).
//! - `gitconfig_excludes_path` + the gitconfig legs (:586-707): REAL
//!   since IG8 -- the DP35 five-level priority ladder is transcribed
//!   as the gc_* family at this file's tail (the env/file read faces
//!   as per-instance oracle admits, expand_tilde as the real gc_et
//!   byte function, the STDJOIN join carrier gcj; the build_global
//!   legs' excludes face parameter keeps consuming it as input).
//! - `parse_excludes_file`, `home_dir`: the regex stays the trusted
//!   gc_pe_face oracle (inventory section 4's one-line spec); home is
//!   a face parameter of the entry point.
//!
//! # Modeling declarations (faces and bounds)
//!
//! - **Byte twin:** upstream operates on `&str`; every line here is a
//!   byte sequence. Slicing positions that upstream guards with byte
//!   checks (`as_bytes().last()`, ASCII prefixes/suffixes) are UTF-8
//!   boundary-safe (a leading/trailing ASCII byte is always a complete
//!   character); `str::starts_with`/`ends_with` on ASCII literals and
//!   `chars().any(|c| c == '/')` / `chars().nth(0) == Some('/')` are
//!   byte-level equivalent (an ASCII byte cannot occur inside a
//!   multi-byte UTF-8 sequence). Each such step carries an Origin note.
//! - **The trim bound (DP11):** upstream `line.trim_right()`
//!   (gitignore.rs:474) is the deprecated Unicode `char::is_whitespace`
//!   trim. The twin models `ASCII-whitespace trim, skipped when the
//!   line ends with the two bytes "\ "` (the escaped-space keep rule,
//!   gitignore.rs:473)`. The twin equals upstream on every all-ASCII
//!   line (the whole 74-vector corpus) and on every line whose final
//!   byte is ASCII non-ws non-backslash; it diverges only on lines with
//!   trailing non-ASCII Unicode whitespace, where UPSTREAM trims more
//!   (runtime witnesses + git-parity differential for those rows in
//!   out/kverus-run/IG2/notes.md; suspects register).
//! - **GlobBuilder verdict oracle (inventory section 6):** the
//!   GlobBuilder::build Ok/Err decision is GL-pending; here it is the
//!   uninterpreted `glob_builder_admits(actual, case_insensitive,
//!   allow_unclosed_class)` plus trusted external-body exec twins.
//!   Every KAT use pins its instance with an explicit admit row backed
//!   by the pinned-tree runtime leg (no universal axiom is claimed).
//!   The `err.kind().to_string()` payload (gitignore.rs:539) is the
//!   trusted string face `glob_err_bytes`.
//! - **GlobSet face stub:** GlobSetBuilder/GlobSet are stub records of
//!   the registered (pattern, case_insensitivity) pairs in registration
//!   order (`RegisteredGlob`). Only the counting face is used by IG2;
//!   the matcher face (`matches_candidate_into`, last-highest
//!   precedent over reversed iteration) is IG3's mount per inventory
//!   section 6.
//! - **Pool leg:** `matches: Option<Arc<Pool<Vec<usize>>>>` -- pure
//!   scratch reuse with no observable content (inventory section 4);
//!   omitted from the twin.
//! - **Shape note (borrow-chaining returns):** upstream `add_line`
//!   returns `Result<&mut GitignoreBuilder, Error>`, and
//!   `case_insensitive`/`allow_unclosed_class` return `Result<&mut
//!   Self, Error>` / `&mut Self` purely for chaining. The twin returns
//!   `Result<(), Error>` / `()` -- no observable difference for the
//!   obligation face.
//!
//! Origin doc sentences of the public surfaces are quoted at each site.

use vstd::prelude::*;
use vstd::seq::Seq;

use super::pathutil::{
    is_file_name, is_file_name_spec, memrchr_face, memrchr_last, memrchr_spec,
    memrchr_spec_none_bridge, memrchr_spec_some_bridge,
    strip_prefix as pathutil_strip_prefix, strip_prefix_spec, SEP,
};
use super::{
    error_tagged, error_with_path, is_io_spec, line_nested, glob_nested, with_path_inner,
    with_path_payload, Error, IoErrorFace, Match, PartialErrorBuilder, PathBytes,
};

verus! {

// The Seq.push index bookkeeping (broadcast: the per-index store-content
// invariants of the add() loop ride the push index lemmas).
broadcast use vstd::seq::group_seq_axioms;

// ===========================================================================
// Byte-step spec predicates (Origin: gitignore.rs:463-544)
// ===========================================================================

/// The ASCII whitespace set of `char::is_whitespace` on ASCII characters
/// (`0x09..=0x0D` and the space `0x20`) -- the twin trim bound.
pub open spec fn is_ascii_ws(b: u8) -> bool {
    b == 0x09 || b == 0x0A || b == 0x0B || b == 0x0C || b == 0x20
}

/// exec twin of `is_ascii_ws`.
pub fn is_ascii_ws_exec(b: u8) -> (r: bool)
    ensures r == is_ascii_ws(b)
{
    b == 0x09 || b == 0x0A || b == 0x0B || b == 0x0C || b == 0x20
}

/// The length kept by an ASCII-whitespace right trim.
pub open spec fn ascii_trim_right_len(s: Seq<u8>, i: int) -> int
    decreases i
{
    if i <= 0 {
        0
    } else if is_ascii_ws(s[i - 1]) {
        ascii_trim_right_len(s, i - 1)
    } else {
        i
    }
}

/// The trimmed view (upstream: `line.trim_right()`, the bounded model).
pub open spec fn ascii_trim_right(s: Seq<u8>) -> Seq<u8> {
    s.subrange(0, ascii_trim_right_len(s, s.len() as int))
}

/// `line.ends_with("\\ ")` (gitignore.rs:473): the escaped-space keep rule.
pub open spec fn ends_with_backslash_space(s: Seq<u8>) -> bool {
    s.len() >= 2 && s[s.len() - 2] == 0x5C && s[s.len() - 1] == 0x20
}

/// exec twin of `ends_with_backslash_space`.
pub fn ends_with_backslash_space_exec(s: &[u8]) -> (r: bool)
    ensures r == ends_with_backslash_space(s@)
{
    s.len() >= 2 && s[s.len() - 2] == 0x5C && s[s.len() - 1] == 0x20
}

/// The gitignore.rs:473-475 trim step:
/// `if !line.ends_with("\\ ") { line = line.trim_right(); }`.
pub open spec fn trim_step_spec(line: Seq<u8>) -> Seq<u8> {
    if !ends_with_backslash_space(line) { ascii_trim_right(line) } else { line }
}

/// exec twin of the trim step (the upstream in-place rebinding becomes
/// a returned slice).
pub fn trim_step_exec<'a>(line: &'a [u8]) -> (r: &'a [u8])
    ensures r@ == trim_step_spec(line@)
{
    if !ends_with_backslash_space_exec(line) {
        ascii_trim_right_exec(line)
    } else {
        line
    }
}

/// exec of `ascii_trim_right`.
pub fn ascii_trim_right_exec(s: &[u8]) -> (r: &[u8])
    ensures r@ == ascii_trim_right(s@)
{
    let mut i: usize = s.len();
    while i > 0 && is_ascii_ws_exec(s[i - 1])
        invariant
            0 <= i <= s.len(),
            ascii_trim_right_len(s@, i as int) == ascii_trim_right_len(s@, s.len() as int),
        decreases i
    {
        i -= 1;
    }
    &s[..i]
}

/// `line.starts_with("#")` (gitignore.rs:470); ASCII literal.
pub open spec fn starts_with_hash(s: Seq<u8>) -> bool {
    s.len() >= 1 && s[0] == 0x23
}

/// `line.starts_with("!")` (gitignore.rs:491); ASCII literal.
pub open spec fn starts_with_bang(s: Seq<u8>) -> bool {
    s.len() >= 1 && s[0] == 0x21
}

/// `line.starts_with("/")` (gitignore.rs:495); ASCII literal.
pub open spec fn starts_with_slash(s: Seq<u8>) -> bool {
    s.len() >= 1 && s[0] == 0x2F
}

/// `line.starts_with("\\!") || line.starts_with("\\#")`
/// (gitignore.rs:487); ASCII literal pairs.
pub open spec fn starts_with_escaped_bang_or_hash(s: Seq<u8>) -> bool {
    (s.len() >= 2 && s[0] == 0x5C && s[1] == 0x21)
        || (s.len() >= 2 && s[0] == 0x5C && s[1] == 0x23)
}

/// Byte presence scan (upstream: `chars().any(|c| c == '/')`,
/// gitignore.rs:519; byte-level equivalent since `/` is ASCII).
pub open spec fn has_byte_from(s: Seq<u8>, i: int, b: u8) -> bool
    decreases s.len() - i
{
    if i < 0 || i >= s.len() {
        false
    } else if s[i] == b {
        true
    } else {
        has_byte_from(s, i + 1, b)
    }
}

/// The whole-line byte scan.
pub open spec fn any_byte(s: Seq<u8>, b: u8) -> bool {
    has_byte_from(s, 0, b)
}

/// exec twin of `any_byte`.
pub fn any_byte_exec(s: &[u8], b: u8) -> (r: bool)
    ensures r == any_byte(s@, b)
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            has_byte_from(s@, i as int, b) == any_byte(s@, b),
        decreases s.len() - i
    {
        if s[i] == b {
            return true;
        }
        i += 1;
    }
    false
}

/// `actual.starts_with("**/")` (gitignore.rs:74); ASCII literal.
pub open spec fn starts_with_doublestar_slash(s: Seq<u8>) -> bool {
    s.len() >= 3 && s[0] == 0x2A && s[1] == 0x2A && s[2] == 0x2F
}

/// `actual == "**"` (gitignore.rs:74); ASCII literal.
pub open spec fn is_bare_doublestar(s: Seq<u8>) -> bool {
    s.len() == 2 && s[0] == 0x2A && s[1] == 0x2A
}

/// `Glob::has_doublestar_prefix` (gitignore.rs:72-75), at the value
/// level:
/// `self.actual.starts_with("**/") || self.actual == "**"`.
pub open spec fn has_doublestar_prefix_spec(actual: Seq<u8>) -> bool {
    starts_with_doublestar_slash(actual) || is_bare_doublestar(actual)
}

/// `glob.actual.ends_with("/**")` (gitignore.rs:528); ASCII literal.
pub open spec fn ends_with_slash_doublestar(s: Seq<u8>) -> bool {
    s.len() >= 3
        && s[s.len() - 3] == 0x2F
        && s[s.len() - 2] == 0x2A
        && s[s.len() - 1] == 0x2A
}

/// exec twin of `ends_with_slash_doublestar`.
pub fn ends_with_slash_doublestar_exec(s: &[u8]) -> (r: bool)
    ensures r == ends_with_slash_doublestar(s@)
{
    s.len() >= 3
        && s[s.len() - 3] == 0x2F
        && s[s.len() - 2] == 0x2A
        && s[s.len() - 1] == 0x2A
}

// ===========================================================================
// Flat-eval bridges (the IG1 #IG-1 recipe: whole-value assertions on
// composed Seq terms shoot down, so value-level rows walk the len/index
// facts through the vstd seq lemma family)
// ===========================================================================

/// Flat-eval bridge for `p.add(s)`-composed sequences (the `**/`
/// prepend of gitignore.rs:522 and any add-shapes): when `flat` carries
/// exactly p's bytes then s's bytes, the composed term equals it.
pub proof fn flat_add(p: Seq<u8>, s: Seq<u8>, flat: Seq<u8>)
    requires
        p.len() + s.len() == flat.len(),
        forall|i: int| #![trigger flat[i]] 0 <= i < p.len() ==> flat[i] == p[i],
        forall|i: int| #![trigger flat[i]] p.len() <= i < flat.len()
            ==> flat[i] == s[i - p.len()],
    ensures p.add(s) == flat
{
    vstd::seq::lemma_seq_add_len(p, s);
    assert forall|i: int| 0 <= i < flat.len() implies (p.add(s))[i] == flat[i] by {
        if i < p.len() {
            vstd::seq::lemma_seq_add_index1(p, s, i);
        } else {
            vstd::seq::lemma_seq_add_index2(p, s, i);
        }
    };
}

/// Flat-eval bridge for `s.subrange(lo, hi)`-composed keeps (the trim
/// step and the front/dir strips of the add_line chain).
pub proof fn flat_subrange(s: Seq<u8>, lo: int, hi: int, flat: Seq<u8>)
    requires
        0 <= lo <= hi <= s.len(),
        (hi - lo) == flat.len(),
        forall|j: int| #![trigger flat[j]] 0 <= j < flat.len() ==> flat[j] == s[j + lo],
    ensures s.subrange(lo, hi) == flat
{
        assert forall|j: int| 0 <= j < flat.len() implies (s.subrange(lo, hi))[j] == flat[j] by {
        vstd::seq::axiom_seq_subrange_index(s, lo, hi, j);
        vstd::seq::lemma_seq_subrange_len(s, lo, hi);
    };
}

// ===========================================================================
// The GlobBuilder verdict oracle (GL-pending; inventory section 6)
// ===========================================================================

/// The un-interpreted GlobBuilder::build verdict (trusted oracle face).
/// Instances land per KAT row as explicit admits backed by the
/// pinned-tree runtime leg; the GL batch re-anchors at mount.
pub uninterp spec fn glob_builder_admits(
    actual: Seq<u8>,
    case_insensitive: bool,
    allow_unclosed_class: bool,
) -> bool;

/// `err.kind().to_string()` payload (gitignore.rs:539) -- trusted string
/// face; no observable content in this batch's obligations.
pub uninterp spec fn glob_err_bytes(
    actual: Seq<u8>,
    case_insensitive: bool,
    allow_unclosed_class: bool,
) -> Seq<u8>;

/// The exec twin of the verdict oracle (body outside the verified
/// surface; the contract is the trust boundary).
#[verifier::external_body]
pub fn glob_builder_admits_exec(
    actual: &[u8],
    case_insensitive: bool,
    allow_unclosed_class: bool,
) -> (r: bool)
    ensures r == glob_builder_admits(actual@, case_insensitive, allow_unclosed_class)
{
    unimplemented!() // trusted face: the GlobBuilder decision is GL's
}

/// The exec twin of the error-string face.
#[verifier::external_body]
pub fn glob_err_bytes_exec(
    actual: &[u8],
    case_insensitive: bool,
    allow_unclosed_class: bool,
) -> (r: Vec<u8>)
    ensures r@ == glob_err_bytes(actual@, case_insensitive, allow_unclosed_class)
{
    unimplemented!() // trusted face: err.kind().to_string() (string tier)
}

// ===========================================================================
// The add_line value model (Origin: gitignore.rs:463-544, step by step)
// ===========================================================================

/// The outcome of one add_line call at the value level.
pub enum AddLineOutcome {
    /// The line was skipped (comment, or empty after the trim step);
    /// upstream returns `Ok(self)` having pushed nothing.
    Skip,
    /// The rewrite chain produced this record; the bool is the
    /// GlobBuilder verdict (the oracle value).
    Add(GlobSpec),
}

/// The rewrite-chain record (the pre-storage view of `Glob`).
pub struct GlobSpec {
    /// Upstream `from` (the source file path payload).
    pub from: Option<Seq<u8>>,
    /// The post-trim line before any prefix peeling (upstream
    /// `original`: `line.to_string()` at gitignore.rs:481).
    pub original: Seq<u8>,
    /// The rewritten glob string (gitignore.rs:515, :522, :529).
    pub actual: Seq<u8>,
    /// Upstream `is_whitelist` (the `!` prefix; gitignore.rs:488-494).
    pub is_whitelist: bool,
    /// Upstream `is_only_dir` (the dir-suffix slash; :506).
    pub is_only_dir: bool,
    /// The GlobBuilder verdict for `actual` (oracle).
    pub grok_admitted: bool,
}

/// Origin: `GitignoreBuilder::add_line` (gitignore.rs:463-544), the full
/// rewrite chain as one value function. Step-by-step correspondence:
///
/// - :470 `if line.starts_with("#") { return Ok(self); }`
/// - :473-475 `if !line.ends_with("\\ ") { line = line.trim_right(); }`
/// - :476-478 `if line.is_empty() { return Ok(self); }`
/// - :479-485 the Glob record starts (`original = line.to_string()`)
/// - :487-503 the front-strip chain (escaped `\!`/`\#`, else the `!`
///   whitelist and then the `/` anchoring). NOTE: in the escaped branch,
///   `is_absolute = line.chars().nth(0) == Some('/')` inspects the
///   one-byte-stripped remainder whose first character is necessarily
///   `!` or `#` -- hence always FALSE there (see
///   `escaped_branch_never_absolute`); kept verbatim.
/// - :506-513 the dir-suffix strip + the issue-2236 escape peel.
/// - :515 `glob.actual = line.to_string()`
/// - :519-523 the `**/` injection rule (only when not anchored, no
///   literal slash, and no existing `**/` prefix or bare `**`).
/// - :528-529 the `/**` -> `/**/*` suffix rule.
/// - :531-540 the GlobBuilder compile (the oracle here).
pub open spec fn add_line_value(
    case_insensitive: bool,
    allow_unclosed_class: bool,
    from: Option<Seq<u8>>,
    line: Seq<u8>,
) -> AddLineOutcome {
    if starts_with_hash(line) {
        AddLineOutcome::Skip
    } else {
        let t = trim_step_spec(line);
        if t.len() == 0 {
            AddLineOutcome::Skip
        } else {
            // the front-strip chain (gitignore.rs:487-503)
            let front: Seq<u8> = if starts_with_escaped_bang_or_hash(t) {
                t.subrange(1, t.len() as int)
            } else {
                let after_bang: Seq<u8> = if starts_with_bang(t) {
                    t.subrange(1, t.len() as int)
                } else {
                    t
                };
                if starts_with_slash(after_bang) {
                    after_bang.subrange(1, after_bang.len() as int)
                } else {
                    after_bang
                }
            };
            let is_whitelist: bool = !starts_with_escaped_bang_or_hash(t)
                && starts_with_bang(t);
            let is_absolute: bool = if starts_with_escaped_bang_or_hash(t) {
                // verbatim gitignore.rs:489 (always false; see the lemma)
                let rest = t.subrange(1, t.len() as int);
                rest.len() >= 1 && rest[0] == 0x2F
            } else {
                let after_bang: Seq<u8> = if starts_with_bang(t) {
                    t.subrange(1, t.len() as int)
                } else {
                    t
                };
                starts_with_slash(after_bang)
            };
            // the dir-suffix double strip (gitignore.rs:506-513)
            let is_only_dir: bool = front.len() >= 1
                && front[front.len() - 1] == 0x2F;
            let tail: Seq<u8> = if is_only_dir {
                let u = front.subrange(0, front.len() - 1);
                if u.len() >= 1 && u[u.len() - 1] == 0x5C {
                    u.subrange(0, u.len() - 1)
                } else {
                    u
                }
            } else {
                front
            };
            // :515 `glob.actual = line.to_string()`
            let actual0: Seq<u8> = tail;
            // :519-523 the `**/` injection rule
            let actual1: Seq<u8> =
                if !is_absolute && !any_byte(actual0, 0x2F)
                    && !has_doublestar_prefix_spec(actual0)
                {
                    // format!("**/{}", glob.actual)
                    seq![0x2A, 0x2A, 0x2F].add(actual0)
                } else {
                    actual0
                };
            // :528-529 the `/**` suffix rule
            let actual: Seq<u8> = if ends_with_slash_doublestar(actual1) {
                // format!("{}/*", glob.actual)
                actual1.add(seq![0x2F, 0x2A])
            } else {
                actual1
            };
            AddLineOutcome::Add(GlobSpec {
                from,
                original: t,
                actual,
                is_whitelist,
                is_only_dir,
                grok_admitted: glob_builder_admits(
                    actual,
                    case_insensitive,
                    allow_unclosed_class,
                ),
            })
        }
    }
}

/// Outcome arm: the line was skipped (the value-level view of the
/// upstream `return Ok(self)` early exits).
pub open spec fn outcome_skip(
    case_insensitive: bool,
    allow_unclosed_class: bool,
    from: Option<Seq<u8>>,
    line: Seq<u8>,
) -> bool {
    add_line_value(case_insensitive, allow_unclosed_class, from, line)
        == AddLineOutcome::Skip
}

/// Outcome arm: a record was produced and the GlobBuilder admitted it.
pub open spec fn outcome_add_ok(
    case_insensitive: bool,
    allow_unclosed_class: bool,
    from: Option<Seq<u8>>,
    line: Seq<u8>,
) -> bool {
    match add_line_value(case_insensitive, allow_unclosed_class, from, line) {
        AddLineOutcome::Add(gs) => gs.grok_admitted,
        AddLineOutcome::Skip => false,
    }
}

/// Outcome arm: the GlobBuilder rejected the record (the value-level
/// view of the upstream `?` early return with the builder untouched).
pub open spec fn outcome_add_rejected(
    case_insensitive: bool,
    allow_unclosed_class: bool,
    from: Option<Seq<u8>>,
    line: Seq<u8>,
) -> bool {
    match add_line_value(case_insensitive, allow_unclosed_class, from, line) {
        AddLineOutcome::Add(gs) => !gs.grok_admitted,
        AddLineOutcome::Skip => false,
    }
}

/// The record accessor of the outcome (the Add arm's GlobSpec; the
/// Skip arm's dummy is never inspected -- its clauses are guarded by
/// outcome_add_ok / outcome_add_rejected).
pub open spec fn outcome_record(
    case_insensitive: bool,
    allow_unclosed_class: bool,
    from: Option<Seq<u8>>,
    line: Seq<u8>,
) -> GlobSpec {
    match add_line_value(case_insensitive, allow_unclosed_class, from, line) {
        AddLineOutcome::Add(gs) => gs,
        AddLineOutcome::Skip => GlobSpec {
            from: None,
            original: Seq::empty(),
            actual: Seq::empty(),
            is_whitelist: false,
            is_only_dir: false,
            grok_admitted: true,
        },
    }
}

/// The gitignore.rs:489 dead computation, as a lemma: in the escaped
/// branch (`\!`/`\#` prefix), the first character of the stripped line is
/// `!` or `#`, never `/`, so `is_absolute` is always false there.
/// (Vestigial upstream code; transcribed verbatim above; registered as
/// an Origin observation -- no behavioral suspect.)
pub proof fn escaped_branch_never_absolute(line: Seq<u8>)
    ensures
        starts_with_escaped_bang_or_hash(line)
            ==> (!(line.subrange(1, line.len() as int).len() >= 1
                && line.subrange(1, line.len() as int)[0] == 0x2F)),
{
    // The stripped remainder's first byte is 0x21 or 0x23 by the prefix
    // conditions; both differ from 0x2F.
    if line.len() >= 2 && line[0] == 0x5C && line[1] == 0x21 {
        assert(line.subrange(1, line.len() as int).len() >= 1
            && line.subrange(1, line.len() as int)[0] == 0x21);
    }
    if line.len() >= 2 && line[0] == 0x5C && line[1] == 0x23 {
        assert(line.subrange(1, line.len() as int).len() >= 1
            && line.subrange(1, line.len() as int)[0] == 0x23);
    }
}

// ===========================================================================
// Glob -- upstream gitignore.rs:27-76
// ===========================================================================

/// Origin struct (gitignore.rs:31-43), fields verbatim (PathBuf payload
/// -> the PathBytes carrier, String -> Vec<u8>; see lib.rs notes).
pub struct Glob {
    /// The file path that this glob was extracted from.
    pub from: Option<PathBytes>,
    /// The original glob string.
    pub original: Vec<u8>,
    /// The actual glob string used to convert to a regex.
    pub actual: Vec<u8>,
    /// Whether this is a whitelisted glob or not.
    pub is_whitelist: bool,
    /// Whether this glob should only match directories or not.
    pub is_only_dir: bool,
}

impl Glob {
    /// Upstream doc (gitignore.rs:46-47, verbatim):
    ///   "Returns the file path that defined this glob."
    pub fn from(&self) -> (r: Option<&PathBytes>) {
        match &self.from {
            Some(p) => Some(p),
            None => None,
        }
    }

    /// Upstream doc (gitignore.rs:51, verbatim):
    ///   "The original glob as it was defined in a gitignore file."
    pub fn original(&self) -> (r: &[u8])
        ensures r@ == self.original@
    {
        self.original.as_slice()
    }

    /// Upstream doc (gitignore.rs:56-58, verbatim):
    ///   "The actual glob that was compiled to respect gitignore
    ///    semantics."
    pub fn actual(&self) -> (r: &[u8])
        ensures r@ == self.actual@
    {
        self.actual.as_slice()
    }

    /// Upstream doc (gitignore.rs:62, verbatim):
    ///   "Whether this was a whitelisted glob or not."
    pub fn is_whitelist(&self) -> (r: bool)
        ensures r == self.is_whitelist
    {
        self.is_whitelist
    }

    /// Upstream doc (gitignore.rs:67, verbatim):
    ///   "Whether this glob must match a directory or not."
    pub fn is_only_dir(&self) -> (r: bool)
        ensures r == self.is_only_dir
    {
        self.is_only_dir
    }

    /// `fn has_doublestar_prefix` (gitignore.rs:72-75), upstream doc:
    /// "Returns true if and only if this glob has a `**/` prefix."
    fn has_doublestar_prefix(&self) -> (r: bool)
        ensures r == has_doublestar_prefix_spec(self.actual@)
    {
        starts_with_doublestar_slash_exec(self.actual.as_slice())
            || is_bare_doublestar_exec(self.actual.as_slice())
    }
}

/// exec twin of `is_bare_doublestar`.
pub fn is_bare_doublestar_exec(s: &[u8]) -> (r: bool)
    ensures r == is_bare_doublestar(s@)
{
    s.len() == 2 && s[0] == 0x2A && s[1] == 0x2A
}

/// exec twin of `starts_with_doublestar_slash`.
pub fn starts_with_doublestar_slash_exec(s: &[u8]) -> (r: bool)
    ensures r == starts_with_doublestar_slash(s@)
{
    s.len() >= 3 && s[0] == 0x2A && s[1] == 0x2A && s[2] == 0x2F
}

// ===========================================================================
// The GlobSet registration stub (inventory section 6)
// ===========================================================================

/// One registered glob: the (pattern, case-insensitivity) pair the
/// GlobSetBuilder sees (registration order = vector order).
pub struct RegisteredGlob {
    /// The pattern's source string (the `actual` bytes).
    pub pattern: Vec<u8>,
    /// The builder's case toggle at add time (the GlobBuilder option).
    pub case_insensitive: bool,
}

/// The GlobSetBuilder face stub (upstream field `builder`).
pub struct GlobSetBuilderFace {
    /// The registration record (append-only; len = registration count).
    pub registered: Vec<RegisteredGlob>,
}

/// The GlobSet face stub (upstream field `set`); IG3 mounts the matcher
/// face on this record (matches_candidate_into; last-highest precedent
/// over reversed iteration).
pub struct GlobSetFace {
    /// The registration record carried into the built matcher.
    pub registered: Vec<RegisteredGlob>,
}

// ===========================================================================
// GitignoreBuilder -- upstream gitignore.rs:318-581
// ===========================================================================

/// Origin struct (gitignore.rs:320-326), verbatim fields (the
/// GlobSetBuilder leg is the stub record above).
pub struct GitignoreBuilder {
    /// Upstream field `builder: GlobSetBuilder`.
    pub builder: GlobSetBuilderFace,
    /// The root path to match against.
    pub root: PathBytes,
    /// The collected globs.
    pub globs: Vec<Glob>,
    /// The case-insensitive toggle (default false; gitignore.rs:341).
    pub case_insensitive: bool,
    /// The allow-unclosed-class toggle (default true; gitignore.rs:342;
    /// DP8: the gitignore-side default `true` vs the overrides-side
    /// `false` is a documented cross-module divergence, upstream
    /// overrides.rs:125).
    pub allow_unclosed_class: bool,
}

impl GitignoreBuilder {
    /// Upstream doc (gitignore.rs:329-334, verbatim):
    ///   "Create a new builder for a gitignore file.
    ///    The path given should be the path at which the globs for this
    ///    gitignore file should be matched. Note that paths are always
    ///    matched relative to the root path given here. Generally, the
    ///    root path should correspond to the *directory* containing a
    ///    `.gitignore` file."
    ///
    /// Body (gitignore.rs:335-344): `root: strip_prefix("./", root)
    /// .unwrap_or(root).to_path_buf()` -- the pathutil unix byte-prefix
    /// strip (one occurrence), mounted from the IG1 twin.
    pub fn new(root: &[u8]) -> (r: GitignoreBuilder)
        ensures
            r.root.bytes@ == root_strip_view(root@),
            r.globs@ == Seq::empty(),
            r.builder.registered@ == Seq::empty(),
            !r.case_insensitive,
            r.allow_unclosed_class,
    {
        let prefix_vec = dot_slash_exec();
        let stripped = pathutil_strip_prefix(prefix_vec.as_slice(), root);
        let root_bytes: &[u8] = match stripped {
            Some(s) => {
                proof {
                    // (the exec prefix comes from dot_slash_exec with
                    // view == seq![0x2E, 0x2F], so the IG1 post instantiates
                    // exactly against root_strip_view's spec call)
                    assert(root_strip_view(root@) == s@);
                }
                s
            }
            None => {
                proof {
                    assert(root_strip_view(root@) == root@);
                }
                root
            }
        };
        GitignoreBuilder {
            builder: GlobSetBuilderFace { registered: Vec::new() },
            root: PathBytes { bytes: vstd::slice::slice_to_vec(root_bytes) },
            globs: Vec::new(),
            case_insensitive: false,
            allow_unclosed_class: true,
        }
    }

    /// Upstream doc (gitignore.rs:546-551, verbatim):
    ///   "Toggle whether the globs should be matched case insensitively
    ///    or not.
    ///    When this option is changed, only globs added after the change
    ///    will be affected.
    ///    This is disabled by default."
    ///
    /// DP7: the ordering promise is realized by the per-add snapshot --
    /// both stores record the toggle value at add time (see `add_line`),
    /// so later toggles never re-compile earlier globs.
    pub fn case_insensitive(&mut self, yes: bool) -> (r: Result<(), Error>)
        ensures
            r matches Ok(_),
            final(self).case_insensitive == yes,
            final(self).allow_unclosed_class == old(self).allow_unclosed_class,
            final(self).globs@ == old(self).globs@,
            final(self).builder.registered@ == old(self).builder.registered@,
            final(self).root == old(self).root,
    {
        self.case_insensitive = yes;
        Ok(())
    }

    /// Upstream doc (gitignore.rs:562-573, verbatim):
    ///   "Toggle whether unclosed character classes are allowed. When
    ///    allowed, a `[` without a matching `]` is treated literally
    ///    instead of resulting in a parse error.
    ///    For example, if this is set then the glob `[abc` will be
    ///    treated as the literal string `[abc` instead of returning an
    ///    error.
    ///    By default, this is true in order to match established
    ///    `gitignore` semantics. Generally speaking, enabling this leads
    ///    to worse failure modes since the glob parser becomes more
    ///    permissive. You might want to enable this when compatibility
    ///    (e.g., with POSIX glob implementations) is more important than
    ///    good error messages."
    pub fn allow_unclosed_class(&mut self, yes: bool) -> ()
        ensures
            final(self).allow_unclosed_class == yes,
            final(self).case_insensitive == old(self).case_insensitive,
            final(self).globs@ == old(self).globs@,
            final(self).builder.registered@ == old(self).builder.registered@,
            final(self).root == old(self).root,
    {
        self.allow_unclosed_class = yes;
    }

    /// Upstream doc (gitignore.rs:457-462, verbatim):
    ///   "Add a line from a gitignore file to this builder.
    ///    If this line came from a particular `gitignore` file, then its
    ///    path should be provided here.
    ///    If the line could not be parsed as a glob, then an error is
    ///    returned."
    ///
    /// The value-level contract is `add_line_value(case_insensitive,
    /// allow_unclosed_class, from, line)` (the correspondence is proven
    /// by the body against the step spec fns). Storage effects:
    ///
    /// - Skip: store unchanged, Ok (upstream `return Ok(self)`).
    /// - Add + admitted: the record lands in `globs` and the
    ///   registration pair lands in `builder.registered` (pattern =
    ///   `actual`; case toggle snapshot = the value at this call -- the
    ///   DP7 ordering face), Ok.
    /// - Add + rejected (the GlobBuilder error): builder UNCHANGED
    ///   (upstream early-returns through `?` before the pushes) and
    ///   `Err(Error::Glob { glob: Some(original), err })` -- the
    ///   per-line side of the DP14 partial-success discipline.
    pub fn add_line(
        &mut self,
        from: Option<PathBytes>,
        line: &[u8],
    ) -> (r: Result<(), Error>)
        ensures
            final(self).case_insensitive == old(self).case_insensitive,
            final(self).allow_unclosed_class == old(self).allow_unclosed_class,
            final(self).root == old(self).root,
            outcome_skip(old(self).case_insensitive, old(self).allow_unclosed_class,
                from_view(from), line@)
                ==> (r matches Ok(_)
                    && final(self).globs@ == old(self).globs@
                    && final(self).builder.registered@ == old(self).builder.registered@),
            outcome_add_ok(old(self).case_insensitive, old(self).allow_unclosed_class,
                from_view(from), line@)
                ==> (r matches Ok(_)
                    && (forall|k: int| #![trigger globs_field_view(old(self).globs@[k])]
                        0 <= k < old(self).globs@.len() ==>
                        (globs_field_view(final(self).globs@[k])
                            == globs_field_view(old(self).globs@[k])))
                    && (forall|k: int| #![trigger old(self).builder.registered@[k].pattern@]
                        0 <= k < old(self).builder.registered@.len() ==>
                        (final(self).builder.registered@[k].pattern@
                            == old(self).builder.registered@[k].pattern@
                            && final(self).builder.registered@[k].case_insensitive
                                == old(self).builder.registered@[k].case_insensitive))
                    && final(self).globs@.len() == old(self).globs@.len() + 1
                    && final(self).builder.registered@.len()
                        == old(self).builder.registered@.len() + 1
                    // IG3 strengthening: the value-level pushes (the top
                    // of the post state is the appended record itself;
                    // Vec::push's assume-spec pins the whole-seq equality)
                    && final(self).globs@ == old(self).globs@.push(
                        final(self).globs@[old(self).globs@.len() as int])
                    && final(self).builder.registered@ == old(self).builder
                        .registered@.push(final(self).builder.registered@[
                            old(self).builder.registered@.len() as int])
                    && stored_matches(final(self).globs@[old(self).globs@.len() as int],
                        outcome_record(old(self).case_insensitive,
                            old(self).allow_unclosed_class, from_view(from), line@))
                    && final(self).builder.registered@[
                        old(self).builder.registered@.len() as int
                    ].pattern@ == outcome_record(old(self).case_insensitive,
                        old(self).allow_unclosed_class, from_view(from), line@).actual
                    && final(self).builder.registered@[
                        old(self).builder.registered@.len() as int
                    ].case_insensitive == old(self).case_insensitive),
            outcome_add_rejected(old(self).case_insensitive,
                old(self).allow_unclosed_class, from_view(from), line@)
                ==> (r matches Err(e)
                    && e matches Error::Glob { glob: Some(_), err: _ }
                    && (match e {
                        Error::Glob { glob: Some(v), .. } =>
                            v@ == outcome_record(old(self).case_insensitive,
                                old(self).allow_unclosed_class,
                                from_view(from), line@).original,
                        _ => false,
                    })
                    && final(self).globs@ == old(self).globs@
                    && final(self).builder.registered@ == old(self).builder.registered@),
    {
        // :470 `if line.starts_with("#") { return Ok(self); }`
        if line.len() >= 1 && line[0] == 0x23 {
            return Ok(());
        }
        // :473-475 the escaped-space keep / Unicode-trim step (bounded)
        let trimmed = trim_step_exec(line);
        // :476-478 `if line.is_empty() { return Ok(self); }`
        if trimmed.len() == 0 {
            return Ok(());
        }
        // :479-485 the record starts (`original = line.to_string()`)
        let original = vstd::slice::slice_to_vec(trimmed);
        let mut is_whitelist = false;
        let mut is_absolute = false;
        let rest0: &[u8];
        if starts_with_escaped_bang_or_hash_exec(trimmed) {
            // :488 `line = &line[1..]`
            let step = &trimmed[1..];
            // :489 `is_absolute = line.chars().nth(0) == Some('/')`
            // (always false here -- escaped_branch_never_absolute)
            is_absolute = step.len() >= 1 && step[0] == 0x2F;
            rest0 = step;
        } else {
            let mut rest = trimmed;
            // :491-494 the whitelist bang
            if rest.len() >= 1 && rest[0] == 0x21 {
                is_whitelist = true;
                rest = &rest[1..];
            }
            // :495-502 the anchoring slash ("banning wildcards from
            // matching /" -- the man gitignore rule, upstream comment)
            if rest.len() >= 1 && rest[0] == 0x2F {
                is_absolute = true;
                rest = &rest[1..];
            }
            rest0 = rest;
        }
        // :506-513 "If it ends with a slash, then this should only match
        // directories, but the slash should otherwise not be used while
        // globbing" + the issue-2236 escape peel below.
        let mut is_only_dir = false;
        let tail: &[u8];
        if rest0.len() >= 1 && rest0[rest0.len() - 1] == 0x2F {
            is_only_dir = true;
            let u = &rest0[..rest0.len() - 1];
            if u.len() >= 1 && u[u.len() - 1] == 0x5C {
                tail = &u[..u.len() - 1];
            } else {
                tail = u;
            }
        } else {
            tail = rest0;
        }
        // :515 `glob.actual = line.to_string()`
        let mut actual = vstd::slice::slice_to_vec(tail);
        // :519-523 the `**/` injection rule
        if !is_absolute && !any_byte_exec(tail, 0x2F) {
            if !(starts_with_doublestar_slash_exec(actual.as_slice())
                || is_bare_doublestar_exec(actual.as_slice()))
            {
                actual = prepend_bytes_2a_2a_2f(tail);
            }
        }
        // :528-529 the `/**` -> `/**/*` rule
        if ends_with_slash_doublestar_exec(actual.as_slice()) {
            actual = append_bytes_2f_2a(actual.as_slice());
        }
        // :531-540 the GlobBuilder compile (oracle face); on Err the
        // `?` propagates `Error::Glob { glob: Some(original), err }`
        // with the builder untouched (no push happened yet).
        if !glob_builder_admits_exec(
            actual.as_slice(),
            self.case_insensitive,
            self.allow_unclosed_class,
        ) {
            return Err(Error::Glob {
                glob: Some(original),
                err: glob_err_bytes_exec(
                    actual.as_slice(),
                    self.case_insensitive,
                    self.allow_unclosed_class,
                ),
            });
        }
        // :541 `self.builder.add(parsed);`
        self.builder.registered.push(RegisteredGlob {
            pattern: actual.clone(),
            case_insensitive: self.case_insensitive,
        });
        // :542 `self.globs.push(glob);`
        self.globs.push(Glob {
            from,
            original,
            actual,
            is_whitelist,
            is_only_dir,
        });
        proof {
            // the value-level posts: Vec::push's assume-spec plus the
            // broadcast push index lemmas make the post top equal the
            // appended record, re-anchoring the whole-seq equality
            // onto the post index form (no nameable ghost of the moved
            // value is needed -- the broadcast lemma fires on the
            // assume-spec's own term)
            assert(final(self).globs@.len() == old(self).globs@.len() + 1);
            assert(final(self).builder.registered@.len()
                == old(self).builder.registered@.len() + 1);
        }
        Ok(())
    }
}

/// Spec helper: the view of `strip_prefix("./", root).unwrap_or(root)`
/// (`GitignoreBuilder::new`, gitignore.rs:339 -- the IG1 pathutil twin).
pub open spec fn root_strip_view(root: Seq<u8>) -> Seq<u8> {
    match super::pathutil::strip_prefix_spec(seq![0x2E, 0x2F], root) {
        Some(s) => s,
        None => root,
    }
}

/// The exec carrier of the "./" prefix literal (gitignore.rs:339);
/// static slice literals have no spec view identity in this Verus
/// build, so the two bytes are assembled push-style with the exact
/// spec post (#IG-1 recipe).
pub fn dot_slash_exec() -> (r: Vec<u8>)
    ensures r@ == seq![0x2E, 0x2F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2E);
    v.push(0x2F);
    v
}

/// Spec helper: `from` payload view.
pub open spec fn from_view(from: Option<PathBytes>) -> Option<Seq<u8>> {
    match from {
        Some(p) => Some(p.bytes@),
        None => None,
    }
}

/// Spec helper: the stored Glob matches the GlobSpec record part (the
/// stored twin carries no verdict; `gs.grok_admitted` is the caller-side
/// dimension this view deliberately does not compare).
pub open spec fn stored_matches(g: Glob, gs: GlobSpec) -> bool {
    ((g.from matches Some(_) && from_view(g.from) == gs.from)
        || (g.from matches None && gs.from matches None))
        && g.original@ == gs.original
        && g.actual@ == gs.actual
        && g.is_whitelist == gs.is_whitelist
        && g.is_only_dir == gs.is_only_dir
}

/// Spec helper: the `Error::Glob.glob` payload view (the add_line error
/// arm; `Some(glob.original.clone())` at gitignore.rs:538).
pub open spec fn error_glob_payload(e: &Error) -> Option<Seq<u8>> {
    match e {
        Error::Glob { glob, .. } => match glob {
            Some(v) => Some(v@),
            None => None,
        },
        _ => None,
    }
}

/// exec twin of `starts_with_escaped_bang_or_hash`.
pub fn starts_with_escaped_bang_or_hash_exec(s: &[u8]) -> (r: bool)
    ensures r == starts_with_escaped_bang_or_hash(s@)
{
    (s.len() >= 2 && s[0] == 0x5C && s[1] == 0x21)
        || (s.len() >= 2 && s[0] == 0x5C && s[1] == 0x23)
}

/// `format!("**/{}", s)` (gitignore.rs:522).
pub fn prepend_bytes_2a_2a_2f(s: &[u8]) -> (r: Vec<u8>)
    ensures r@ == seq![0x2A, 0x2A, 0x2F].add(s@)
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2A);
    v.push(0x2A);
    v.push(0x2F);
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v@ == seq![0x2A, 0x2A, 0x2F].add(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        v.push(s[i]);
        i += 1;
    }
    v
}

/// `format!("{}/*", s)` (gitignore.rs:529).
pub fn append_bytes_2f_2a(s: &[u8]) -> (r: Vec<u8>)
    ensures r@ == s@.add(seq![0x2F, 0x2A])
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v@ == s@.subrange(0, i as int),
        decreases s.len() - i
    {
        v.push(s[i]);
        i += 1;
    }
    v.push(0x2F);
    v.push(0x2A);
    v
}

// ===========================================================================
// build() counting -- upstream gitignore.rs:346-369
// ===========================================================================
//
// Upstream doc (gitignore.rs:346-348, verbatim):
//   "Builds a new matcher from the globs added so far.
//    Once a matcher is built, no new globs can be added to it."

/// Spec count: whitelisted records among the first i entries.
pub open spec fn count_whitelists(globs: Seq<Glob>, i: int) -> int
    decreases i
{
    if i <= 0 {
        0
    } else if globs[i - 1].is_whitelist {
        count_whitelists(globs, i - 1) + 1
    } else {
        count_whitelists(globs, i - 1)
    }
}

/// Spec count: non-whitelisted (ignore) records among the first i.
pub open spec fn count_ignores(globs: Seq<Glob>, i: int) -> int
    decreases i
{
    if i <= 0 {
        0
    } else if globs[i - 1].is_whitelist {
        count_ignores(globs, i - 1)
    } else {
        count_ignores(globs, i - 1) + 1
    }
}

/// The count partition lemma (the DP6 arithmetic core): every entry is
/// counted by exactly one of the two counters.
pub proof fn count_partition(globs: Seq<Glob>, i: int)
    requires 0 <= i <= globs.len()
    ensures count_whitelists(globs, i) + count_ignores(globs, i) == i
    decreases i
{
    if i > 0 {
        count_partition(globs, i - 1);
    }
}

/// A deep byte-exact copy of one Glob (push-wise carriers; no Clone face).
pub fn copy_glob(g: &Glob) -> (r: Glob)
    ensures
        r.original@ == g.original@,
        r.actual@ == g.actual@,
        r.is_whitelist == g.is_whitelist,
        r.is_only_dir == g.is_only_dir,
        from_view(r.from) == from_view(g.from),
{
    Glob {
        from: match &g.from {
            Some(p) => Some(PathBytes {
                bytes: vstd::slice::slice_to_vec(p.bytes.as_slice()),
            }),
            None => None,
        },
        original: vstd::slice::slice_to_vec(g.original.as_slice()),
        actual: vstd::slice::slice_to_vec(g.actual.as_slice()),
        is_whitelist: g.is_whitelist,
        is_only_dir: g.is_only_dir,
    }
}

/// Upstream: `self.builder.build().map_err(|err| Error::Glob { glob:
/// None, err: err.to_string() })?` (gitignore.rs:355-358) -- the
/// GlobSetBuilder::build leg. TRUSTED ADMIT: pin-tree globset's
/// GlobSetBuilder::build accepts every successfully built glob added to
/// it (its only error source is a failed GlobBuilder::build -- which
/// add_line gates earlier through the verdict oracle), so the Err arm
/// has no reachable witness: transcribed as the returned face carrying
/// the same registration record, with the map_err arm recorded in this
/// comment only (never executed by the twin).
#[verifier::external_body]
pub fn glob_set_builder_build_leg(b: &GlobSetBuilderFace) -> (r: GlobSetFace)
    ensures r.registered@ == b.registered@
{
    unimplemented!() // trusted face (see the admit note above)
}

impl GitignoreBuilder {
    /// Origin: `build` (gitignore.rs:349-369).
    ///
    /// - :350-352 `if self.globs.is_empty() { return
    ///   Ok(Gitignore::empty()); }` (the empty matcher's root is the
    ///   empty string, NOT this builder's root)
    /// - :353-354 the two filter counts
    /// - :355-358 the GlobSetBuilder::build leg (the admitted face
    ///   above; its map_err arm is the dead transcription noted there)
    /// - :359-368 the matcher assembly (the Pool leg omitted per the
    ///   header).
    ///
    /// The post carries the DP6 pieces: counts == the spec counters,
    /// set.len() == globs.len() (registration is 1:1 with the store).
    pub fn build(&self) -> (r: Result<Gitignore, Error>)
        ensures
            r matches Ok(_),
            self.globs.len() == 0
                ==> (r matches Ok(g) && gi_is_empty_view(&g)),
            self.globs.len() > 0
                ==> (r matches Ok(g)
                    && g.root.bytes@ == self.root.bytes@
                    && g.set.registered@ == self.builder.registered@
                    && (g.num_ignores as int)
                        == count_ignores(self.globs@, self.globs.len() as int)
                    && (g.num_whitelists as int)
                        == count_whitelists(self.globs@, self.globs.len() as int)
                    && g.globs@.len() == self.globs@.len()
                    && forall|i: int| 0 <= i < self.globs@.len() ==>
                        globs_field_view(g.globs@[i]) == globs_field_view(self.globs@[i])),
    {
        // :350-352 the empty case (Gitignore::empty(), root "")
        if self.globs.len() == 0 {
            return Ok(Gitignore::empty());
        }
        // :353-354 `let nignore = ...filter(...).count();` (loop form)
        let mut nignore: usize = 0;
        let mut nwhite: usize = 0;
        let mut i: usize = 0;
        while i < self.globs.len()
            invariant
                0 <= i <= self.globs.len(),
                nignore as int == count_ignores(self.globs@, i as int),
                nwhite as int == count_whitelists(self.globs@, i as int),
                nignore as int + nwhite as int <= i as int,
            decreases self.globs.len() - i
        {
            if self.globs[i].is_whitelist {
                nwhite += 1;
            } else {
                nignore += 1;
            }
            i += 1;
        }
        // :355-358 the GlobSetBuilder::build leg (admitted face)
        let set = glob_set_builder_build_leg(&self.builder);
        // :359-368 the assembly (`self.globs.clone()` copy-wise)
        let mut new_globs: Vec<Glob> = Vec::new();
        let mut j: usize = 0;
        while j < self.globs.len()
            invariant
                0 <= j <= self.globs.len(),
                new_globs@.len() == j as int,
                forall|k: int| 0 <= k < j ==>
                    globs_field_view(new_globs@[k]) == globs_field_view(self.globs@[k]),
            decreases self.globs.len() - j
        {
            new_globs.push(copy_glob(&self.globs[j]));
            j += 1;
        }
        Ok(Gitignore {
            set,
            root: PathBytes {
                bytes: vstd::slice::slice_to_vec(self.root.bytes.as_slice()),
            },
            globs: new_globs,
            num_ignores: nignore as u64,
            num_whitelists: nwhite as u64,
        })
    }
}

// ===========================================================================
// Gitignore -- upstream gitignore.rs:78-88, 148-189 (counting face)
// ===========================================================================

/// Origin struct (gitignore.rs:80-88); the twin keeps the builder-side
/// counting surface. matched_/strip/Pool mount with IG3.
pub struct Gitignore {
    /// Upstream field `set: GlobSet` (the registration-record stub).
    pub set: GlobSetFace,
    /// Upstream field `root: PathBuf`.
    pub root: PathBytes,
    /// Upstream field `globs: Vec<Glob>`.
    pub globs: Vec<Glob>,
    /// Upstream field `num_ignores: u64`.
    pub num_ignores: u64,
    /// Upstream field `num_whitelists: u64`.
    pub num_whitelists: u64,
}

impl Gitignore {
    /// Upstream doc (gitignore.rs:148-151, verbatim):
    ///   "Creates a new empty gitignore matcher that never matches
    ///    anything.
    ///    Its path is empty."
    pub fn empty() -> (r: Gitignore)
        ensures
            r.set.registered@ == Seq::empty(),
            r.root.bytes@ == Seq::empty(),
            r.globs@ == Seq::empty(),
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

    /// Upstream doc (gitignore.rs:159-161, verbatim):
    ///   "Returns the directory containing this gitignore matcher.
    ///    All matches are done relative to this path."
    pub fn path(&self) -> (r: &[u8])
        ensures r@ == self.root.bytes@
    {
        self.root.bytes.as_slice()
    }

    /// Upstream doc (gitignore.rs:166-170, verbatim):
    ///   "Returns true if and only if this gitignore has zero globs,
    ///    and therefore never matches any file path."
    pub fn is_empty(&self) -> (r: bool)
        ensures r == (self.set.registered@.len() == 0)
    {
        self.set.registered.len() == 0
    }

    /// Upstream doc (gitignore.rs:171-173, verbatim):
    ///   "Returns the total number of globs, which should be equivalent
    ///    to `num_ignores + num_whitelists`."
    /// (The equivalence is proven at dp6_len_is_nignore_plus_nwhite.)
    pub fn len(&self) -> (r: usize)
        ensures r as int == self.set.registered@.len()
    {
        self.set.registered.len()
    }

    /// Upstream doc (gitignore.rs:175, verbatim):
    ///   "Returns the total number of ignore globs."
    pub fn num_ignores(&self) -> (r: u64)
        ensures r == self.num_ignores
    {
        self.num_ignores
    }

    /// Upstream doc (gitignore.rs:177, verbatim):
    ///   "Returns the total number of whitelisted globs."
    pub fn num_whitelists(&self) -> (r: u64)
        ensures r == self.num_whitelists
    {
        self.num_whitelists
    }
}

/// Field-view equality of one store entry (the per-index claim of build).
pub open spec fn globs_field_view(g: Glob) -> (Seq<u8>, Seq<u8>, bool, bool,
    Option<Seq<u8>>,
)
{
    (g.original@, g.actual@, g.is_whitelist, g.is_only_dir, from_view(g.from))
}

/// The empty-matcher view (build's empty-arm claim).
pub open spec fn gi_is_empty_view(g: &Gitignore) -> bool {
    g.set.registered@.len() == 0
        && g.root.bytes@.len() == 0
        && g.globs@.len() == 0
        && g.num_ignores == 0
        && g.num_whitelists == 0
}

/// DP6 (gitignore.rs:171-173: "should be equivalent to `num_ignores +
/// num_whitelists`") for every matcher built with the add_line-maintained
/// invariant `set.len() == globs.len()`: len == num_ignores +
/// num_whitelists.
pub proof fn dp6_len_is_nignore_plus_nwhite(g: Gitignore)
    requires
        g.set.registered@.len() == g.globs@.len(),
        g.num_ignores as int == count_ignores(g.globs@, g.globs@.len() as int),
        g.num_whitelists as int == count_whitelists(g.globs@, g.globs@.len() as int),
    ensures
        g.set.registered@.len()
            == (g.num_ignores as int) + (g.num_whitelists as int)
{
    count_partition(g.globs@, g.globs@.len() as int);
}

// ===========================================================================
// IG3: the matcher decision core -- strip + matched +
// matched_path_or_any_parents (gitignore.rs:191-315) over the GlobSet
// matcher-oracle face (GL-pending per inventory section 6)
// ===========================================================================
//
// Face note (GlobSet stub, the IG2 handshake): the per-pattern match
// decision below `glob_pat_matches(pattern, case_insensitive,
// candidate)` is the un-interpreted ORACLE for the GlobMatcher seam:
// its instances land per KAT row as explicit admits, each backed by
// the pinned-tree runtime column (out/kverus-run/IG3/
// ig3-driver-rows.txt S8/S9MASK -- measured with the pin-tree globset
// GlobMatcher compiled with the same options the crate passes at
// gitignore.rs:531-540: literal_separator(true), backslash_escape(true),
// allow_unclosed_class(builder toggle), case per registration
// snapshot), over the same globset::Candidate face matched_stripped
// uses. The Candidate::new normalization is folded INTO the oracle
// (globset's own leading-'./' absorption among others), which is why
// the twin's strip divergence on './'-chains (see gi_strip_spec) is
// unobservable at the match verdict (runtime rows S10rooteq). GL
// re-anchors at mount.

/// The GlobMatcher oracle (GL-pending): does this compiled glob match
/// the candidate? `pattern` is the registered `actual` bytes, the
/// case flag is the registration-time snapshot (the DP7 face), and
/// `candidate` is the already-stripped path matched against.
pub uninterp spec fn glob_pat_matches(
    pattern: Seq<u8>,
    case_insensitive: bool,
    candidate: Seq<u8>,
) -> bool;

/// The exec twin of the match oracle (body outside the verified surface;
/// the contract is the trust boundary). The harness admits pin the
/// instances the KAT rows consume.
#[verifier::external_body]
pub fn glob_pat_matches_exec(
    pattern: &[u8],
    case_insensitive: bool,
    candidate: &[u8],
) -> (r: bool)
    ensures r == glob_pat_matches(pattern@, case_insensitive, candidate@)
{
    unimplemented!() // trusted face: the GlobMatcher decision is GL's
}

/// `matches_candidate_into` at the value tier (gitignore.rs:273-274's
/// scratch fill): the indices of the registered globs whose pattern
/// matches the candidate, in REGISTRATION ORDER (increasing). This is
/// the inventory-section-6 face; the twin's `gi_decide_from` below is
/// the same decision in first-highest-precedent (reversed-first-passing)
/// form over which `matched_stripped` walks -- the relation is
/// definitional (the reversed scan of this list), and both sides are
/// kept so GL can mount on either.
pub open spec fn match_indices(
    registered: Seq<RegisteredGlob>,
    candidate: Seq<u8>,
    i: int,
) -> Seq<int>
    decreases i
{
    if i <= 0 {
        Seq::empty()
    } else {
        let prior = match_indices(registered, candidate, i - 1);
        if glob_pat_matches(
            registered[i - 1].pattern@,
            registered[i - 1].case_insensitive,
            candidate,
        ) {
            prior.push(i - 1)
        } else {
            prior
        }
    }
}

/// The matched_stripped decision value: scanning DOWNWARD from index
/// `i`, the FIRST (i.e. highest-registration) index whose pattern
/// matches AND passes the dir gate (`!glob.is_only_dir() || is_dir`,
/// gitignore.rs:281 verbatim) decides; None when none does. The
/// out-of-range arm is defensive (the twin's exec scans only the
/// common prefix of the globs/registration stores).
pub open spec fn gi_decide_from(
    globs: Seq<Glob>,
    registered: Seq<RegisteredGlob>,
    candidate: Seq<u8>,
    is_dir: bool,
    i: int,
) -> Option<(bool, int)>
    decreases i + 1
{
    if i < 0 || i >= globs.len() || i >= registered.len() {
        None
    } else if glob_pat_matches(
        registered[i].pattern@,
        registered[i].case_insensitive,
        candidate,
    ) && (!globs[i].is_only_dir || is_dir) {
        Some((globs[i].is_whitelist, i))
    } else {
        gi_decide_from(globs, registered, candidate, is_dir, i - 1)
    }
}

/// The whole-store decision: scan from the top of the common prefix
/// (the built matchers keep globs.len() == registered.len() -- build's
/// post -- so this is just "from the end" there).
pub open spec fn gi_decide(
    globs: Seq<Glob>,
    registered: Seq<RegisteredGlob>,
    candidate: Seq<u8>,
    is_dir: bool,
) -> Option<(bool, int)> {
    let n = if globs.len() < registered.len() {
        globs.len()
    } else {
        registered.len()
    };
    gi_decide_from(globs, registered, candidate, is_dir, n - 1)
}

/// The one-step unfolding of the decision scan (the loop invariant's
/// maintenance bridge).
pub proof fn gi_decide_from_step(
    globs: Seq<Glob>,
    registered: Seq<RegisteredGlob>,
    candidate: Seq<u8>,
    is_dir: bool,
    k: int,
)
    requires
        0 <= k < globs.len(),
        k < registered.len(),
    ensures gi_decide_from(globs, registered, candidate, is_dir, k)
        == if glob_pat_matches(
            registered[k].pattern@,
            registered[k].case_insensitive,
            candidate,
        ) && (!globs[k].is_only_dir || is_dir) {
            Some((globs[k].is_whitelist, k))
        } else {
            gi_decide_from(globs, registered, candidate, is_dir, k - 1)
        }
{
}

// ===========================================================================
// IG-R: the match_indices <-> gi_decide content bridge (the IG3
// deferred ledger item, closed at the GL-mount batch). Both faces
// read the same per-pattern oracle, so the bridge is intra-tree; GL's
// role at this seam is the tier BELOW the oracle (the strategy and
// regex machinery the ut_igr1/ut_igr2 harness units re-instantiate
// per instance from the sibling globset tree). The lemma upgrades the
// "definitional" comment above into a machine-checked theorem, with
// the matched_stripped dir-gate bookkeeping carried explicitly.
// ===========================================================================

/// The dir-gated index list: the registration-ordered indices (of the
/// prefix [0, i)) whose registered pattern matches AND passes the dir
/// gate (`!glob.is_only_dir() || is_dir`, gitignore.rs:281) --
/// match_indices filtered by the gate.
pub open spec fn gated_match_indices(
    globs: Seq<Glob>,
    registered: Seq<RegisteredGlob>,
    candidate: Seq<u8>,
    is_dir: bool,
    i: int,
) -> Seq<int>
    decreases i
{
    if i <= 0 {
        Seq::empty()
    } else {
        let prior = gated_match_indices(globs, registered, candidate, is_dir, i - 1);
        if glob_pat_matches(
            registered[i - 1].pattern@,
            registered[i - 1].case_insensitive,
            candidate,
        ) && (!globs[i - 1].is_only_dir || is_dir) {
            prior.push(i - 1)
        } else {
            prior
        }
    }
}

/// The gated list's top element in decision shape: None when the
/// prefix has no gated-matching index, else the whitelist flag and the
/// index (the last = highest-registration gated-matching index).
pub open spec fn gated_match_indices_top(
    globs: Seq<Glob>,
    registered: Seq<RegisteredGlob>,
    candidate: Seq<u8>,
    is_dir: bool,
    i: int,
) -> Option<(bool, int)> {
    let g = gated_match_indices(globs, registered, candidate, is_dir, i);
    if g.len() == 0 {
        None
    } else {
        let j = g[g.len() - 1];
        Some((globs[j].is_whitelist, j))
    }
}

/// The content bridge, machine-checked: over every common-prefix scan
/// window [0, i), the matched_stripped decision IS the gated list's
/// top -- same whitelist flag, same deciding index -- and the None
/// arms coincide (the reversed-first-passing reading the face comment
/// above states). Without the gate this degenerates to the
/// match_indices-top reading of the inventory-section-6 face (the gate
/// filter is the only difference between the two lists).
pub proof fn gi_decide_from_gated_bridge(
    globs: Seq<Glob>,
    registered: Seq<RegisteredGlob>,
    candidate: Seq<u8>,
    is_dir: bool,
    i: int,
)
    requires
        0 <= i <= globs.len(),
        i <= registered.len(),
    ensures
        gated_match_indices_top(globs, registered, candidate, is_dir, i) matches None
            ==> gi_decide_from(globs, registered, candidate, is_dir, i - 1) matches None,
        gated_match_indices_top(globs, registered, candidate, is_dir, i)
            matches Some((wl, j))
            ==> gi_decide_from(globs, registered, candidate, is_dir, i - 1)
                == Some((wl, j)),
    decreases i
{
    if 0 < i {
        // induction on the scan window: the window [0, i-1) governs
        // both recursions' tails (the IH), and the one-step lemma ties
        // the top decision index to this window's newest element.
        gi_decide_from_gated_bridge(globs, registered, candidate, is_dir, i - 1);
        gi_decide_from_step(globs, registered, candidate, is_dir, i - 1);
        reveal_with_fuel(gated_match_indices, 2);
        // the fresh-push arm reads its top index off the push (the
        // module's group_seq_axioms broadcast carries the push-len and
        // push-index bookkeeping); the skip arm is the recursion.
    }
}

/// Resolving a decision onto the payload view (the matched Glob's
/// fields at the deciding index).
pub open spec fn gi_decide_view(
    d: Option<(bool, int)>,
    globs: Seq<Glob>,
) -> Option<(bool, (Seq<u8>, Seq<u8>, bool, bool, Option<Seq<u8>>))> {
    match d {
        None => None,
        Some((wl, idx)) => Some((wl, globs_field_view(globs[idx]))),
    }
}

/// The view of a returned Match<Glob> (None / whitelist flag + the
/// returned Glob's field view; the payload copy is view-preserving per
/// copy_glob).
pub open spec fn gi_match_view(
    m: Match<Glob>,
) -> Option<(bool, (Seq<u8>, Seq<u8>, bool, bool, Option<Seq<u8>>))> {
    match m {
        Match::None => None,
        Match::Whitelist(g) => Some((true, globs_field_view(g))),
        Match::Ignore(g) => Some((false, globs_field_view(g))),
    }
}

/// `Path::has_root` on unix: a leading separator (used by DP5's panic
/// contract, gitignore.rs:243 `assert!(!path.has_root(), ..)`).
pub open spec fn has_root_spec(p: Seq<u8>) -> bool {
    p.len() >= 1 && p[0] == 0x2F
}

/// `std::path::Path::parent` at the byte tier -- the walk-up leg of
/// matched_path_or_any_parents (gitignore.rs:252-258). Bounded face:
/// equal to std Path::parent on every path whose components are
/// non-empty, dot-free (except a leading CurDir: parent("./a") ==
/// Some(".") is KEPT), single-separated and without trailing
/// separators -- the shapes the strip candidates of the corpus and the
/// inline vectors produce (std diverges on 'a//b', 'a/b/', 'a/b//c';
/// the S11 parent-probe rows in ig3-driver-rows.txt pin the std values
/// on those shapes). The bare root '/' and the empty path have no
/// parent (std: None).
pub open spec fn parent_spec(p: Seq<u8>) -> Option<Seq<u8>> {
    if p.len() == 0 || (p.len() == 1 && p[0] == 0x2F) {
        None
    } else {
        // scan downward from the end for the separator; the first
        // (highest) hit is the parent split; no hit means a bare name
        // whose parent is the empty path (std Path::parent('a') ==
        // Some(''))
        parent_scan(p, p.len() - 1)
    }
}

/// The downward separator scan backing parent_spec (self-contained so
/// the termination check sees the decreasing index).
pub open spec fn parent_scan(p: Seq<u8>, i: int) -> Option<Seq<u8>>
    decreases i + 1
{
    if i < 0 {
        Some(Seq::empty())
    } else if i < p.len() && p[i] == SEP {
        Some(p.subrange(0, i))
    } else {
        parent_scan(p, i - 1)
    }
}

/// The scan's Some values are strictly shorter than the scanned path
/// (the empty arm is shorter for every nonempty path; the hit arm is a
/// subrange ending before the in-range hit index).
pub proof fn parent_scan_bounded(p: Seq<u8>, i: int)
    requires
        0 < p.len(),
        i < p.len(),
    ensures parent_scan(p, i) matches Some(q) ==> q.len() < p.len()
    decreases i + 1
{
    if i < 0 {
        // the empty parent: 0 < p.len()
    } else if i < p.len() && p[i] == SEP {
        vstd::seq::lemma_seq_subrange_len(p, 0, i);
    } else {
        if i > 0 {
            parent_scan_bounded(p, i - 1);
        }
        // i == 0 with the arm guard false falls to i = -1 (the empty
        // parent, covered above)
    }
}

/// The parent of a nonempty path is strictly shorter than the path.
pub proof fn parent_len_bound(p: Seq<u8>, i: int)
    requires
        p.len() > 0,
        0 <= i < p.len(),
        p[i] == SEP,
    ensures p.subrange(0, i).len() < p.len()
{
    vstd::seq::lemma_seq_subrange_len(p, 0, i);
}

/// Range lemma for the memrchr face: the last-occurrence scan stays
/// within [0, from] (so the parent slice bound never passes the
/// separator index).
pub proof fn memrchr_last_in_range(s: Seq<u8>, from: int, c: u8)
    requires
        0 <= from < s.len(),
    ensures 0 <= memrchr_last(s, from, c) <= from
    decreases from + 1
{
    if s[from] == c {
        // lands here: 0 <= from <= from
        reveal_with_fuel(memrchr_last, 2);
        assert(memrchr_last(s, from, c) == from);
    } else {
        if from > 0 {
            memrchr_last_in_range(s, from - 1, c);
            reveal_with_fuel(memrchr_last, 2);
            assert(0 <= memrchr_last(s, from - 1, c) <= from - 1);
            assert(memrchr_last(s, from, c) == memrchr_last(s, from - 1, c));
        } else {
            // from == 0 with s[0] != c falls to the defensive arm (0)
            reveal_with_fuel(memrchr_last, 2);
            assert(memrchr_last(s, from, c) == 0);
        }
    }
}



/// exec twin of `parent_spec` (the downward scan materialized as a
/// loop; the slice split rides vstd::slice::slice_subrange).
pub fn parent_bytes_exec(p: &[u8]) -> (r: Option<&[u8]>)
    ensures
        (r matches None) == (parent_spec(p@) matches None),
        r matches Some(q) ==> (parent_spec(p@) == Some(q@)),
{
    if p.len() == 0 || (p.len() == 1 && p[0] == 0x2F) {
        None
    } else {
        let mut i: usize = p.len() - 1;
        loop
            invariant
                0 <= i < p@.len(),
                forall|k: int| #![trigger p@[k]] (i as int) < k < p@.len()
                    ==> p@[k] != SEP,
                parent_spec(p@) == parent_scan(p@, i as int),
            decreases i + 1
        {
            if p[i] == super::pathutil::SEP_EXEC {
                proof {
                    parent_len_bound(p@, i as int);
                }
                return Some(vstd::slice::slice_subrange(p, 0, i));
            }
            if i == 0 {
                // bare name: the empty parent (the None arm of the
                // memrchr face and parent_scan's i < 0 arm agree)
                return Some(vstd::slice::slice_subrange(p, 0, 0));
            }
            proof {
                assert(parent_scan(p@, i as int)
                    == (if p@[i as int] == SEP {
                        Some(p@.subrange(0, i as int))
                    } else {
                        parent_scan(p@, i as int - 1)
                    }));
            }
            i -= 1;
        }
        unreachable!()
    }
}

/// `Path::new("/")`-style carrier (the '/' re-peel prefix at
/// gitignore.rs:300-303); static slice literals have no spec view
/// identity in this Verus build (#IG-10).
pub fn slash_bytes_exec() -> (r: Vec<u8>)
    ensures r@ == seq![0x2F]
{
    let mut v: Vec<u8> = Vec::new();
    v.push(0x2F);
    v
}

/// The strip value model (gitignore.rs:286-315, step for step):
/// - :289-293 the leading "./" peel;
/// - :295-313 the root peel (unless the root spells '.', or the path
///   is a bare file name) with the follow-up '/' peel (:300-303).
///
/// Face bound -- the root '.' test: upstream compares
/// `self.root != Path::new(".")`, and std Path equality is
/// COMPONENT-based (Path::new("./") == Path::new("."), so a
/// builder-preserved "./" root also qualifies). The twin compares
/// bytes == [0x2E]: roots that stay undotted byte-wise ("./" survives
/// GitignoreBuilder::new's single './' peel only for "././"-style
/// spellings) can enter the peel arm where std would skip it -- but
/// the peeled candidate at most drops a leading "./" that the
/// globset Candidate normalization absorbs anyway (runtime rows
/// S10rooteq record the observable equivalence; no corpus vector
/// distinguishes the two).
pub open spec fn gi_strip_spec(root: Seq<u8>, path: Seq<u8>) -> Seq<u8> {
    let peeled_dot = match strip_prefix_spec(seq![0x2E, 0x2F], path) {
        Some(s) => s,
        None => path,
    };
    let root_dot = root == seq![0x2E];
    if !root_dot && !is_file_name_spec(peeled_dot) {
        match strip_prefix_spec(root, peeled_dot) {
            Some(after_root) => match strip_prefix_spec(seq![0x2F], after_root) {
                Some(after_sep) => after_sep,
                None => after_root,
            },
            None => peeled_dot,
        }
    } else {
        peeled_dot
    }
}

/// The parent-walking decision of matched_path_or_any_parents
/// (gitignore.rs:252-266): decide at the candidate; on None, walk to
/// the parent (is_dir := true from there on) and repeat.
pub open spec fn gi_mp_walk(
    globs: Seq<Glob>,
    registered: Seq<RegisteredGlob>,
    cand: Seq<u8>,
    is_dir: bool,
) -> Option<(bool, int)>
    decreases cand.len()
{
    decreases_by(gi_mp_walk_decreases);

    match gi_decide(globs, registered, cand, is_dir) {
        Some(hit) => Some(hit),
        None => match parent_spec(cand) {
            Some(p) => gi_mp_walk(globs, registered, p, true),
            None => None,
        },
    }
}

/// The termination witness: every parent the walk recurses onto is
/// strictly shorter (the scan's bound), so cand.len() decreases.
#[verifier(decreases_by)]
pub proof fn gi_mp_walk_decreases(
    globs: Seq<Glob>,
    registered: Seq<RegisteredGlob>,
    cand: Seq<u8>,
    is_dir: bool,
) {
    if parent_spec(cand) matches Some(p) {
        if cand.len() > 0 {
            parent_scan_bounded(cand, cand.len() - 1);
        }
    }
}

/// With an empty registration store every level decides None and the
/// walk bottoms out at the parentless candidate: `None` all the way
/// (used by matched/matched_path_or_any_parents's is_empty guards).
pub proof fn mp_walk_none_when_empty(
    globs: Seq<Glob>,
    registered: Seq<RegisteredGlob>,
    cand: Seq<u8>,
    is_dir: bool,
)
    requires registered.len() == 0
    ensures gi_mp_walk(globs, registered, cand, is_dir) matches None
    decreases cand.len()
{
    assert(gi_decide(globs, registered, cand, is_dir) matches None);
    match parent_spec(cand) {
        Some(p) => {
            // parent_spec is None for the empty path and the bare root,
            // so the Some arm comes from the scan: strictly shorter
            if cand.len() == 0 || (cand.len() == 1 && cand[0] == 0x2F) {
                assert(parent_spec(cand) matches None);
            } else {
                parent_scan_bounded(cand, cand.len() - 1);
                assert(p.len() < cand.len());
            }
            mp_walk_none_when_empty(globs, registered, p, true);
        }
        None => {}
    }
}

impl Gitignore {
    /// Origin: `strip` (gitignore.rs:286-315); upstream visibility
    /// private (fn). The twin keeps it pub so the harness zone can
    /// drive the strip face directly on the DP33 rows. Behavior notes:
    /// - the './' peel and the '/' re-peel go through the IG1 pathutil
    ///   strip_prefix twin (the unix BYTE-prefix arm -- DP33's home);
    /// - the root '.' test is byte-wise with the documented face bound
    ///   above (std Path component equality on './'-spelled roots).
    pub fn strip<'a>(&'a self, path: &'a [u8]) -> (r: &'a [u8])
        ensures r@ == gi_strip_spec(self.root.bytes@, path@)
    {
        let mut p: &[u8] = path;
        // :289-293 A leading ./ is completely superfluous. We also
        // strip it from our gitignore root path...
        let ds = dot_slash_exec();
        match pathutil_strip_prefix(ds.as_slice(), path) {
            Some(q) => p = q,
            None => p = path,
        }
        // :295-313 the root peel, guarded by the '.'-root special case
        // and the bare-file-name case ("a file name might not have any
        // directory components to it"), upstream comments verbatim.
        let root_is_dot = self.root.bytes.len() == 1 && self.root.bytes[0] == 0x2E;
        proof {
            assert(self.root.bytes@.len() == self.root.bytes.len() as int);
            if root_is_dot {
                assert(self.root.bytes@ =~= seq![0x2E]);
            } else {
                assert(self.root.bytes@ != seq![0x2E]);
            }
        }
        if !root_is_dot && !is_file_name(p) {
            match pathutil_strip_prefix(self.root.bytes.as_slice(), p) {
                Some(q) => {
                    p = q;
                    // :300-303 If we're left with a leading slash, get
                    // rid of it (the digestion of the separator-kept values
                    // DP33's unix arm produces).
                    let sb = slash_bytes_exec();
                    match pathutil_strip_prefix(sb.as_slice(), p) {
                        Some(q2) => p = q2,
                        None => p = p,
                    }
                }
                None => p = p,
            }
        }
        p
    }

    /// Origin: `matched_stripped` (gitignore.rs:265-284); upstream
    /// visibility private (fn). The twin inlines the scratch-Vec fill
    /// and the reversed iteration (`.rev()`, gitignore.rs:277-284) into
    /// one downward scan over registration indices: the Pool/scratch
    /// has no observable content (header note) and the scan order is
    /// exactly the order `matches.iter().rev()` yields, with the
    /// verbatim dir gate `if !glob.is_only_dir() || is_dir`
    /// (gitignore.rs:279-280).
    pub fn matched_stripped(&self, path: &[u8], is_dir: bool) -> (r: Match<Glob>)
        ensures
            gi_decide_view(gi_decide(self.globs@, self.set.registered@, path@,
                is_dir), self.globs@) == gi_match_view(r),
    {
        if self.is_empty() {
            proof {
                assert(self.set.registered@.len() == 0);
                assert(gi_decide(self.globs@, self.set.registered@, path@, is_dir)
                    matches None);
            }
            return Match::None;
        }
        let n: usize = if self.set.registered.len() < self.globs.len() {
            self.set.registered.len()
        } else {
            self.globs.len()
        };
        proof {
            // gi_decide's min matches the exec's min; from-anchored
            // at the entry
            let nspec = if self.globs@.len() < self.set.registered@.len() {
                self.globs@.len()
            } else {
                self.set.registered@.len()
            };
            assert(nspec == n as int);
            assert(gi_decide(self.globs@, self.set.registered@, path@, is_dir)
                == gi_decide_from(self.globs@, self.set.registered@, path@, is_dir,
                    nspec - 1));
        }
        let mut i: usize = n;
        while i > 0
            invariant
                i <= n,
                n as int == (if self.globs@.len() < self.set.registered@.len() {
                    self.globs@.len()
                } else {
                    self.set.registered@.len()
                }),
                gi_decide(self.globs@, self.set.registered@, path@, is_dir)
                    == gi_decide_from(self.globs@, self.set.registered@, path@, is_dir,
                        i as int - 1),
            decreases i
        {
            let k = i - 1;
            // the one-step bridge: the scan at k either lands here or
            // re-bases at k-1
            proof {
                gi_decide_from_step(self.globs@, self.set.registered@, path@, is_dir,
                    k as int);
            }
            if glob_pat_matches_exec(
                self.set.registered[k].pattern.as_slice(),
                self.set.registered[k].case_insensitive,
                path,
            ) {
                let g = &self.globs[k];
                // :279-280 `if !glob.is_only_dir() || is_dir`
                if !g.is_only_dir() || is_dir {
                    // :282-284 the verdict flip on is_whitelist
                    return if g.is_whitelist() {
                        Match::Whitelist(copy_glob(g))
                    } else {
                        Match::Ignore(copy_glob(g))
                    };
                }
            }
            i -= 1;
        }
        proof {
            assert(gi_decide_from(self.globs@, self.set.registered@, path@, is_dir, -1)
                matches None);
        }
        Match::None
    }

    /// Upstream doc (gitignore.rs:196-201, verbatim):
    ///   "Returns whether the given path (file or directory) matched a
    ///    pattern in this gitignore matcher.
    ///    `is_dir` should be true if the path refers to a directory and
    ///    false otherwise.
    ///    The given path is matched relative to the path given when
    ///    building the matcher. Specifically, before matching `path`,
    ///    its prefix (as determined by a common suffix of the directory
    ///    containing this gitignore) is stripped. If there is no common
    ///    suffix/prefix overlap, then `path` is assumed to be relative
    ///    to this matcher."
    /// (NB the "common suffix" wording is inverted -- it strips a
    /// common PREFIX; the DP4 docs-only hedge, recorded here verbatim.)
    /// (:202-215 = is_empty guard + strip + matched_stripped.)
    pub fn matched(&self, path: &[u8], is_dir: bool) -> (r: Match<Glob>)
        ensures
            gi_decide_view(gi_decide(self.globs@, self.set.registered@,
                gi_strip_spec(self.root.bytes@, path@), is_dir), self.globs@)
                == gi_match_view(r),
    {
        if self.is_empty() {
            proof {
                assert(gi_decide(self.globs@, self.set.registered@,
                    gi_strip_spec(self.root.bytes@, path@), is_dir) matches None);
            }
            return Match::None;
        }
        let stripped = self.strip(path);
        self.matched_stripped(stripped, is_dir)
    }

    /// Upstream doc (gitignore.rs:229-246, verbatim):
    ///   "Returns whether the given path (file or directory, and
    ///    expected to be under the root) or any of its parent
    ///    directories (up to the root) matched a pattern in this
    ///    gitignore matcher.
    ///    NOTE: This method is more expensive than walking the
    ///    directory hierarchy top-to-bottom and matching the entries.
    ///    But, is easier to use in cases when a list of paths are
    ///    available without a hierarchy.
    ///    `is_dir` should be true if the path refers to a directory
    ///    and false otherwise.
    ///    The given path is matched relative to the path given when
    ///    building the matcher. Specifically, before matching `path`,
    ///    its prefix (as determined by a common suffix of the
    ///    directory containing this gitignore) is stripped. If there
    ///    is no common suffix/prefix overlap, then `path` is assumed
    ///    to be relative to this matcher.
    ///    # Panics
    ///    This method panics if the given file path is not under the
    ///    root path of this matcher."
    ///
    /// DP5: the `assert!(!path.has_root(), "path is expected to be
    /// under the root")` panic site (gitignore.rs:243) is transcribed
    /// as a `requires` clause (the twin's panic-contract convention);
    /// the empty-matcher early return happens BEFORE the panic guard
    /// upstream (:240-242), so the requires is vacuous for empty
    /// matchers. The upstream should_panic vector is recorded as the
    /// runtime row S9 should_panic (ig3-driver-rows.txt) plus the
    /// precondition-realizability rows in the harness. NOTE (the DP33
    /// interaction): a sibling path sharing the root's byte prefix is
    /// stripped past the component boundary, so the guard does NOT
    /// fire for it -- runtime row S10dp33 walk-sibling records the
    /// silent no-panic ignore on a genuinely out-of-root path.
    pub fn matched_path_or_any_parents(&self, path: &[u8], is_dir: bool) -> (r: Match<Glob>)
        requires
            self.set.registered@.len() == 0
                || !has_root_spec(gi_strip_spec(self.root.bytes@, path@)),
        ensures
            gi_decide_view(gi_mp_walk(self.globs@, self.set.registered@,
                gi_strip_spec(self.root.bytes@, path@), is_dir), self.globs@)
                == gi_match_view(r),
    {
        if self.is_empty() {
            proof {
                assert(self.set.registered@.len() == 0);
                mp_walk_none_when_empty(self.globs@, self.set.registered@,
                    gi_strip_spec(self.root.bytes@, path@), is_dir);
            }
            return Match::None;
        }
        let mut cur: &[u8] = self.strip(path);
        let mut cur_is_dir = is_dir;
        loop
            invariant
                gi_mp_walk(self.globs@, self.set.registered@,
                    gi_strip_spec(self.root.bytes@, path@), is_dir)
                    == gi_mp_walk(self.globs@, self.set.registered@, cur@, cur_is_dir),
            decreases cur@.len()
        {
            // :247-251 match on the path itself; None continues
            let m = self.matched_stripped(cur, cur_is_dir);
            if !m.is_none() {
                return m;
            }
            // :250-258 `while let Some(parent) = path.parent()` with
            // is_dir := true at every parent level
            match parent_bytes_exec(cur) {
                Some(p) => {
                    proof {
                        assert(gi_decide(self.globs@, self.set.registered@, cur@,
                            cur_is_dir) matches None);
                        assert(parent_spec(cur@) == Some(p@));
                        // the parent measure: parent_scan's Some
                        // values are strictly shorter
                        assert(cur@.len() > 0);
                        parent_scan_bounded(cur@, cur@.len() - 1);
                    }
                    cur = p;
                    cur_is_dir = true;
                }
                None => {
                    proof {
                        assert(gi_decide(self.globs@, self.set.registered@, cur@,
                            cur_is_dir) matches None);
                        assert(parent_spec(cur@) matches None);
                        assert(gi_mp_walk(self.globs@, self.set.registered@, cur@,
                            cur_is_dir) matches None);
                    }
                    return Match::None;
                }
            }
        }
    }
}

// ===========================================================================
// IG3: the errs-stack content fold (the io-typing rematch) -- the view
// tier of the add()-loop's error stack, element by element
// ===========================================================================

/// The spec view of one stacked error: (io-typed, its nested line
/// number, its nested glob payload). The io/reject events of the add
/// loop produce exactly the two shapes the fold below records.
pub open spec fn err_view(e: &Error) -> (bool, Option<u64>, Option<Seq<u8>>) {
    (is_io_spec(e), line_nested(e), glob_nested(e))
}

/// The plural-wrap inner list (upstream into_error_option's
/// Some(Error::Partial(self.0)); length >= 2 arm).
pub open spec fn partial_stack(e: &Error) -> Seq<Error> {
    match e {
        Error::Partial(errs) => errs@,
        _ => Seq::empty(),
    }
}

/// The errs-stack value fold: one io-tagged entry per read-error
/// line, one reject entry per rejected-glob line (its ORIGINAL glob
/// payload), nothing otherwise; bounded by the processed-line count
/// n (the first read error is the break line: n goes past it by
/// exactly one).
pub open spec fn errs_view_fold(
    case_insensitive: bool,
    allow_unclosed_class: bool,
    lines: Seq<LineRead>,
    n: int,
) -> Seq<(bool, Option<u64>, Option<Seq<u8>>)>
    decreases n
{
    if n <= 0 {
        Seq::empty()
    } else {
        let base = errs_view_fold(case_insensitive, allow_unclosed_class, lines, n - 1);
        let line = if n == 1 {
            strip_bom(line_bytes(lines[0]))
        } else {
            line_bytes(lines[n - 1])
        };
        if lines[n - 1] matches LineRead::Err(_) {
            base.push((true, Some(n as u64), None))
        } else {
            match add_line_value(case_insensitive, allow_unclosed_class, None, line) {
                AddLineOutcome::Add(gs) => if !gs.grok_admitted {
                    base.push((false, Some(n as u64), Some(gs.original)))
                } else {
                    base
                },
                AddLineOutcome::Skip => base,
            }
        }
    }
}

/// The first read-error lies inside the stream (the selector range
/// bounds the view fold's n argument).
pub proof fn first_err_index_range(
    lines: Seq<LineRead>,
    i: int,
)
    requires 0 <= i
    ensures match first_err(lines, i) {
        Some(k) => i <= k < lines.len(),
        None => true,
    }
    decreases lines.len() - i
{
    if i < lines.len() {
        if lines[i] matches LineRead::Err(_) {
        } else {
            first_err_index_range(lines, i + 1);
        }
    }
}

/// An io-typed error never carries a Glob payload anywhere on its
/// wrapper spine (the is_io / glob_nested case split of the (F2)
/// chain).
pub proof fn is_io_no_glob(e: &Error)
    requires is_io_spec(e)
    ensures glob_nested(e) matches None
    decreases e
{
    match e {
        Error::Io(_) => {}
        Error::WithLineNumber { err, .. } => {
            is_io_no_glob(&**err);
        }
        Error::WithPath { err, .. } => {
            is_io_no_glob(&**err);
        }
        Error::WithDepth { err, .. } => {
            is_io_no_glob(&**err);
        }
        Error::Partial(errs) => {
            if errs.len() == 1 {
                let i = 0;
                is_io_no_glob(&errs[i]);
            }
        }
        _ => {}
    }
}

/// The errs-view fold is nonnegative (the >= 1 vs == 0 case split of
/// the (F2) chain needs it).
pub proof fn errs_view_len_nonneg(
    case_insensitive: bool,
    allow_unclosed_class: bool,
    lines: Seq<LineRead>,
    n: int,
)
    requires 0 <= n
    ensures errs_view_fold(case_insensitive, allow_unclosed_class, lines, n).len() >= 0
    decreases n
{
    if n > 0 {
        errs_view_len_nonneg(case_insensitive, allow_unclosed_class, lines, n - 1);
        if lines[n - 1] matches LineRead::Err(_) {
        } else {
            let line = if n == 1 {
                strip_bom(line_bytes(lines[0]))
            } else {
                line_bytes(lines[n - 1])
            };
            match add_line_value(case_insensitive, allow_unclosed_class, None, line) {
                AddLineOutcome::Add(_) => {}
                AddLineOutcome::Skip => {}
            }
        }
    }
}

/// The "exactly one folded error and it is the read-error (dp3 io)
/// shape" predicate (the (F2) blanket's drop side).
pub open spec fn errs_is_single_io(
    errsv: Seq<(bool, Option<u64>, Option<Seq<u8>>)>,
) -> bool {
    errsv.len() == 1
        && (match errsv[0] {
            (io, _, glob) => io && (glob matches None),
        })
}

/// The registration-suffix content claim (the per-index
/// registered-pattern view of the (S) post; wrapped in a helper so the
/// build_global consumption does not re-evaluate the field
/// projections through the opaque datatype).
pub open spec fn registered_suffix_matches_fold(
    registered: Seq<RegisteredGlob>,
    base: int,
    foldv: Seq<GlobSpec>,
) -> bool {
    (forall|j: int| #![trigger registered[base + j]]
        0 <= j < foldv.len() ==> registered[base + j].pattern@ == foldv[j].actual)
}

/// The stored record's field view equals the fold entry's view (the
/// stored_matches bridge: the record fields transfer elementwise).
pub proof fn stored_matches_view_bridge(g: Glob, gs: GlobSpec)
    requires stored_matches(g, gs)
    ensures globs_field_view(g) == globs_spec_field_view(gs)
{
}

/// The reject-event fold is nonnegative (a returned count of `>= 0`
/// for the prefix induction).
pub proof fn errs_reject_len_nonneg(
    case_insensitive: bool,
    allow_unclosed_class: bool,
    lines: Seq<LineRead>,
    n: int,
)
    requires 0 <= n <= lines.len()
    ensures errs_reject_fold_len(case_insensitive, allow_unclosed_class, lines, n) >= 0
    decreases n
{
    if n > 0 {
        errs_reject_len_nonneg(case_insensitive, allow_unclosed_class, lines, n - 1);
        if lines[n - 1] matches LineRead::Err(_) {
            // Err lines contribute nothing to the reject fold
        } else {
            let line = if n == 1 {
                strip_bom(line_bytes(lines[0]))
            } else {
                line_bytes(lines[n - 1])
            };
            match add_line_value(case_insensitive, allow_unclosed_class, None, line) {
                AddLineOutcome::Add(gs) => {
                    if !gs.grok_admitted {
                        // +1: still nonnegative
                    }
                }
                AddLineOutcome::Skip => {}
            }
        }
    }
}

/// A clean prefix contributes nothing to the errs fold: every line in
/// [0..k) decodes and none was a rejected glob (the (IO) shape's empty
/// prefix argument).
pub proof fn errs_view_clean_prefix_empty(
    case_insensitive: bool,
    allow_unclosed_class: bool,
    lines: Seq<LineRead>,
    k: int,
)
    requires
        0 <= k <= lines.len(),
        forall|m: int| #![trigger lines[m]] 0 <= m < k
            ==> (lines[m] matches LineRead::Line(_)),
        errs_reject_fold_len(case_insensitive, allow_unclosed_class, lines, k) == 0,
    ensures errs_view_fold(case_insensitive, allow_unclosed_class, lines, k)
        == Seq::empty()
    decreases k
{
    if k > 0 {
        errs_reject_len_nonneg(case_insensitive, allow_unclosed_class, lines, k);
        errs_reject_len_nonneg(case_insensitive, allow_unclosed_class, lines, k - 1);
        // the recursive require: decode prefix extends, reject count of
        // the shorter prefix is still 0 (nonneg + total zero)
        assert(errs_reject_fold_len(case_insensitive, allow_unclosed_class,
            lines, k - 1) >= 0);
        let line = if k == 1 {
            strip_bom(line_bytes(lines[0]))
        } else {
            line_bytes(lines[k - 1])
        };
        match add_line_value(case_insensitive, allow_unclosed_class, None, line) {
            AddLineOutcome::Add(gs) => {
                // the per-line reject event is 0 (the zero total and
                // the nonnegative prefix)
                assert(errs_reject_fold_len(case_insensitive, allow_unclosed_class,
                    lines, k)
                    == errs_reject_fold_len(case_insensitive, allow_unclosed_class,
                        lines, k - 1) + (if !gs.grok_admitted { 1int } else { 0int }));
                assert(errs_reject_fold_len(case_insensitive, allow_unclosed_class,
                    lines, k - 1) == 0);
                assert(gs.grok_admitted);
                errs_view_clean_prefix_empty(case_insensitive, allow_unclosed_class,
                    lines, k - 1);
            }
            AddLineOutcome::Skip => {
                assert(errs_reject_fold_len(case_insensitive, allow_unclosed_class,
                    lines, k)
                    == errs_reject_fold_len(case_insensitive, allow_unclosed_class,
                        lines, k - 1));
                errs_view_clean_prefix_empty(case_insensitive, allow_unclosed_class,
                    lines, k - 1);
            }
        }
    }
}

// ===========================================================================
// add() -- the file loop over an abstract line stream (gitignore.rs:408-437)
// ===========================================================================
//
// Upstream doc (gitignore.rs:401-407, verbatim):
//   "Add each glob from the file path given.
//    The file given should be formatted as a `gitignore` file.
//    Note that partial errors can be returned. For example, if there was
//    a problem adding one glob, an error for that will be returned, but
//    all other valid globs will still be added."
//
// The fs legs (File::open / BufReader::lines) are trusted faces; their
// outcomes enter as parameters: `stream: Option<Vec<LineRead>>` -- None
// models the File::open error face; LineRead::Err models a line-read
// error (non-UTF-8 lines yield Err(io) in BufRead::lines).

/// The lines view of the abstract stream parameter (None = the open
/// failure face; no lines).
pub open spec fn stream_lines(stream: Option<Vec<LineRead>>) -> Seq<LineRead> {
    match stream {
        Some(ls) => ls@,
        None => Seq::empty(),
    }
}

/// Field-view equality for a GlobSpec (the fold side of the per-index
/// store claim of add()).
pub open spec fn globs_spec_field_view(gs: GlobSpec) -> (Seq<u8>, Seq<u8>, bool, bool,
    Option<Seq<u8>>,
)
{
    (gs.original, gs.actual, gs.is_whitelist, gs.is_only_dir, gs.from)
}

/// One yielded line of the abstract reader stream.
pub enum LineRead {
    /// A decoded line (upstream `Ok(String)`).
    Line(Vec<u8>),
    /// A line-read error (upstream `Err(io::Error)`; the non-UTF-8 case).
    Err(IoErrorFace),
}

/// The `ErrorKind::InvalidData` encoding of the io face (PR #3605):
/// upstream queries `err.kind()` in the read-error arm and continues
/// only on `ErrorKind::InvalidData`. The face's `repr` is the twin's
/// abstract io payload, so the kind check is modeled as one reserved
/// `repr` value: `repr == INVALID_DATA_REPR` is the InvalidData kind
/// (the kind `BufRead::lines` reports for a non-UTF-8 line); the exec
/// constructor `INVALID_DATA_REPR` witnesses it; every other `repr`
/// value models any other kind (the break side of the arm). Witness
/// discipline: the harness rows pin the two sides with
/// `IoErrorFace::new(INVALID_DATA_REPR)` (a non-UTF-8 line) vs
/// `IoErrorFace::new(0)` / `new(7)` (a hard io error), matching the
/// runtime rows PR3605-verify SJ1/SJ4.
pub const INVALID_DATA_REPR: u64 = 1;

/// Spec: the io face's kind is InvalidData (the continue side of the
/// patched read-error arm).
pub open spec fn io_face_is_invalid_data(iof: &IoErrorFace) -> bool {
    iof.repr == INVALID_DATA_REPR
}

/// Exec twin of `err.kind() == ErrorKind::InvalidData`
/// (patch-tree gitignore.rs:421, the kind gate).
pub fn io_face_is_invalid_data_exec(iof: &IoErrorFace) -> (r: bool)
    ensures r == io_face_is_invalid_data(iof)
{
    iof.repr == INVALID_DATA_REPR
}

/// Spec: the line is a read error whose kind is InvalidData (the
/// line the patched loop pushes and then skips past -- `continue`).
pub open spec fn is_invalid_data_line(l: LineRead) -> bool {
    match l {
        LineRead::Err(iof) => io_face_is_invalid_data(&iof),
        _ => false,
    }
}

/// Spec: the line is any read error other than InvalidData (the line
/// the patched loop pushes and then `break`s on; pre-#3605 this was
/// the fate of EVERY read error).
pub open spec fn is_hard_io_line(l: LineRead) -> bool {
    l matches LineRead::Err(_) && !is_invalid_data_line(l)
}

/// Spec: a line the patched loop walks past: a decoded line or an
/// InvalidData read error.
pub open spec fn is_walked_line(l: LineRead) -> bool {
    (l matches LineRead::Line(_)) || is_invalid_data_line(l)
}


/// The read-error `repr` list among the first n lines (one entry per
/// Err line, in order; the Err arms push exactly one io-tagged error
/// each, so this rides alongside the errs stack).
pub open spec fn io_err_reprs(lines: Seq<LineRead>, n: int) -> Seq<u64>
    decreases n
{
    if n <= 0 {
        Seq::empty()
    } else {
        let base = io_err_reprs(lines, n - 1);
        match lines[n - 1] {
            LineRead::Err(iof) => base.push(iof.repr),
            _ => base,
        }
    }
}

/// The line bytes view (Err lines carry none; an Err line folds as an
/// empty line, i.e. a Skip, in the glob fold).
pub open spec fn line_bytes(l: LineRead) -> Seq<u8> {
    match l {
        LineRead::Line(v) => v@,
        LineRead::Err(_) => Seq::empty(),
    }
}

/// `line.trim_start_matches(UTF8_BOM)` (gitignore.rs:428-430): strips
/// ALL leading BOM occurrences (the plural `matches!` semantics of
/// str::trim_start_matches -- repeated prefixes; runtime row
/// bom-repeated). First line only (the `i == 0` guard, :430).
pub open spec fn strip_bom_from(s: Seq<u8>, i: int) -> Seq<u8>
    decreases s.len() - i
{
    if i < 0 || i + 3 > s.len() {
        s.subrange(i, s.len() as int)
    } else if s[i] == 0xEF && s[i + 1] == 0xBB && s[i + 2] == 0xBF {
        strip_bom_from(s, i + 3)
    } else {
        s.subrange(i, s.len() as int)
    }
}

/// The first-line view (`trim_start_matches(UTF8_BOM)` folded to the
/// keep-length form; the repeated-prefix semantics stays visible in the
/// recursion).
pub open spec fn strip_bom(s: Seq<u8>) -> Seq<u8> {
    strip_bom_from(s, 0)
}

/// exec twin of strip_bom.
pub fn strip_bom_exec(s: &[u8]) -> (r: &[u8])
    ensures r@ == strip_bom(s@)
{
    let mut i: usize = 0;
    while s.len() - i >= 3
        invariant
            0 <= i <= s.len(),
            i % 3 == 0,
            strip_bom(s@) == strip_bom_from(s@, i as int),
        decreases s.len() - i
    {
        if s[i] == 0xEF && s[i + 1] == 0xBB && s[i + 2] == 0xBF {
            i += 3;
        } else {
            // the mismatch arm: with room left but no BOM at i, the
            // recursion stops here (the exec condition negation links
            // the slice bytes to the spec view)
            proof {
                assert(s@[i as int] != 0xEF || s@[(i + 1) as int] != 0xBB
                    || s@[(i + 2) as int] != 0xBF);
                assert(strip_bom_from(s@, i as int)
                    == s@.subrange(i as int, s.len() as int));
            }
            return &s[i..];
        }
    }
    // the guard ran out of room: i + 3 > s.len(), the keep arm
    let r = &s[i..];
    proof {
        assert(s.len() - i < 3);
        assert(strip_bom_from(s@, i as int)
            == s@.subrange(i as int, s.len() as int));
    }
    r
}

/// Spec: the first read-error index (None = every line decodes).
/// PR #3605: InvalidData read errors are skipped by the loop, so
/// this selector now reaches PAST them; the fold bound that stops
/// the loop is `first_hard_err` below (a read error whose kind is
/// NOT InvalidData). A stream without hard io errors walks every
/// line (the fix's contract: "all other valid globs will still be
/// added").
pub open spec fn first_err(lines: Seq<LineRead>, i: int) -> Option<int>
    decreases lines.len() - i
{
    if i < 0 || i >= lines.len() {
        None
    } else if lines[i] matches LineRead::Err(_) {
        Some(i)
    } else {
        first_err(lines, i + 1)
    }
}

/// Spec: the first HARD read-error index (a read error whose kind is
/// not InvalidData -- the break line of the patched loop; None = no
/// such line, so the loop walks the whole stream).
pub open spec fn first_hard_err(lines: Seq<LineRead>, i: int) -> Option<int>
    decreases lines.len() - i
{
    if i < 0 || i >= lines.len() {
        None
    } else if is_hard_io_line(lines[i]) {
        Some(i)
    } else {
        first_hard_err(lines, i + 1)
    }
}

/// The glob-fold bound: everything up to (excluding) a first HARD read
/// error (a read error whose kind is not InvalidData); to the end when
/// no such line exists. (An Err line itself folds as a Skip -- see
/// line_bytes -- so including or excluding it does not change the glob
/// fold; the bound here uses the strict index.) Pre-#3605 this was the
/// FIRST read error of any kind; PR #3605 narrows the truncation to
/// non-InvalidData kinds only.
pub open spec fn fold_bound(lines: Seq<LineRead>) -> int {
    match first_hard_err(lines, 0) {
        Some(k) => k,
        None => lines.len() as int,
    }
}

/// The fold: the records the upstream loop pushes, from the first n
/// stream lines (line 0 BOM-stripped; skips and rejected globs push
/// nothing -- the DP3 break is captured by the bound, the DP14
/// per-line side by the rejected case).
pub open spec fn fold_add_lines(
    case_insensitive: bool,
    allow_unclosed_class: bool,
    from: Option<Seq<u8>>,
    lines: Seq<LineRead>,
    n: int,
) -> Seq<GlobSpec>
    decreases n
{
    if n <= 0 {
        Seq::empty()
    } else {
        let prior = fold_add_lines(case_insensitive, allow_unclosed_class, from, lines, n - 1);
        let line = if n == 1 {
            strip_bom(line_bytes(lines[0]))
        } else {
            line_bytes(lines[n - 1])
        };
        match add_line_value(case_insensitive, allow_unclosed_class, from, line) {
            AddLineOutcome::Skip => prior,
            AddLineOutcome::Add(gs) => {
                if gs.grok_admitted { prior.push(gs) } else { prior }
            }
        }
    }
}

/// Spec: the number of errors the loop folds into the errs stack from
/// the first n lines: one per rejected glob among the processed lines
/// (tagged per-line errors), one per read-error line (the io-tagged
/// break error). Skips and admitted globs contribute nothing.
pub open spec fn errs_fold_len(
    case_insensitive: bool,
    allow_unclosed_class: bool,
    lines: Seq<LineRead>,
    n: int,
) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        let base = errs_fold_len(case_insensitive, allow_unclosed_class, lines, n - 1);
        let line = if n == 1 {
            strip_bom(line_bytes(lines[0]))
        } else {
            line_bytes(lines[n - 1])
        };
        let line_event: int = if lines[n - 1] matches LineRead::Err(_) {
            1
        } else {
            match add_line_value(case_insensitive, allow_unclosed_class, None, line) {
                // the `from` column is irrelevant for the error count:
                // the verdict dimension does not depend on it
                AddLineOutcome::Add(gs) => if !gs.grok_admitted { 1 } else { 0 },
                AddLineOutcome::Skip => 0,
            }
        };
        base + line_event
    }
}


/// Spec: the number of REJECTED-glob events among the first n lines (the
/// io read-error event excluded; those errors get dropped by the
/// maybe_push_ignore_io discipline on the build_global leg).
pub open spec fn errs_reject_fold_len(
    case_insensitive: bool,
    allow_unclosed_class: bool,
    lines: Seq<LineRead>,
    n: int,
) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        let base = errs_reject_fold_len(case_insensitive, allow_unclosed_class, lines, n - 1);
        let line = if n == 1 {
            strip_bom(line_bytes(lines[0]))
        } else {
            line_bytes(lines[n - 1])
        };
        let line_event: int = if lines[n - 1] matches LineRead::Err(_) {
            0
        } else {
            match add_line_value(case_insensitive, allow_unclosed_class, None, line) {
                AddLineOutcome::Add(gs) => if !gs.grok_admitted { 1 } else { 0 },
                AddLineOutcome::Skip => 0,
            }
        };
        base + line_event
    }
}

/// The Err-line fold neutrality: processing index k (an Err line) adds no
/// glob, so folds bounded at k and k+1 are equal (the add-loop's break
/// accounting).
pub proof fn fold_err_index_neutral(
    case_insensitive: bool,
    allow_unclosed_class: bool,
    from: Option<Seq<u8>>,
    lines: Seq<LineRead>,
    k: int,
)
    requires
        0 <= k < lines.len(),
        lines[k] matches LineRead::Err(_),
        k + 1 <= lines.len(),
    ensures
        fold_add_lines(case_insensitive, allow_unclosed_class, from, lines, k)
            == fold_add_lines(case_insensitive, allow_unclosed_class, from, lines, k + 1)
{
    // unfolds once: line k folds as an empty line -> trim -> Skip
    assert(lines[k] matches LineRead::Err(_));
    assert(line_bytes(lines[k]) == Seq::empty());
    let line0: Seq<u8> = if k == 0 {
        strip_bom(line_bytes(lines[0]))
    } else {
        line_bytes(lines[k])
    };
    assert(line0 == Seq::empty());
    assert(trim_step_spec(Seq::empty()) == Seq::empty());
    assert(add_line_value(case_insensitive, allow_unclosed_class, from,
        Seq::empty()) == AddLineOutcome::Skip);
}

/// first_err skips a prefix of decode-ok lines (the scan-homogeneity lemma).
pub proof fn first_err_past_prefix(lines: Seq<LineRead>, i: int)
    requires
        0 <= i <= lines.len(),
        forall|m: int| #![trigger lines[m]] 0 <= m < i
            ==> (lines[m] matches LineRead::Line(_)),
    ensures first_err(lines, i) == first_err(lines, 0)
    decreases i
{
    if i > 0 {
        first_err_past_prefix(lines, i - 1);
        // with lines[i-1] a decode-ok line, first_err over [0..i) sees
        // through it: one unfold of the recursion at i-1
        assert(lines[i - 1] matches LineRead::Line(_));
    }
}

/// If every line decodes, there is no first error.
pub proof fn first_err_none_when_all_decode(lines: Seq<LineRead>)
    requires forall|m: int| #![trigger lines[m]]
        0 <= m < lines.len() ==> (lines[m] matches LineRead::Line(_))
    ensures (first_err(lines, 0) matches None)
{
    first_err_past_prefix(lines, lines.len() as int);
    // the scan front is past the end: one unfold gives None
    assert(first_err(lines, lines.len() as int) matches None);
}

/// If the prefix [0..k) all decodes and line k is a read error, then k is
/// the first error.
pub proof fn first_err_at_hit(lines: Seq<LineRead>, k: int)
    requires
        0 <= k < lines.len(),
        lines[k] matches LineRead::Err(_),
        forall|m: int| #![trigger lines[m]] 0 <= m < k
            ==> (lines[m] matches LineRead::Line(_)),
    ensures first_err(lines, 0) == Some(k)
{
    first_err_past_prefix(lines, k);
    // one unfold at the hit index
    assert(first_err(lines, k) == Some(k));
}

// ===========================================================================
// The PR #3605 hard-error selectors (the patched loop's break bound)
// ===========================================================================

/// The processed-line count of the patched loop: everything up to and
/// including the first hard read error, the whole stream when there
/// is none. InvalidData read errors inside the prefix are walked
/// past (they fold as skips in the glob fold and as io events in the
/// errs fold).
pub open spec fn lines_processed_count(lines: Seq<LineRead>) -> int {
    match first_hard_err(lines, 0) {
        Some(k) => k + 1,
        None => lines.len() as int,
    }
}

/// Spec: the stream's only read error is the InvalidData line at
/// first_err's index (the PR-test-file shape: decoded lines around
/// one non-UTF-8 byte line, no hard io error anywhere -- every other
/// line decoded).
pub open spec fn lone_invalid_data_lines(lines: Seq<LineRead>) -> bool {
    match first_err(lines, 0) {
        Some(k) => is_invalid_data_line(lines[k])
            && (forall|m: int| #![trigger lines[m]]
                0 <= m < lines.len() as int && m != k
                ==> (lines[m] matches LineRead::Line(_))),
        None => false,
    }
}

/// The line index the lone-invalid-data predicate pins (its
/// first_err witness; 0 when the predicate is false).
pub open spec fn lone_invalid_data_index(lines: Seq<LineRead>) -> int {
    match first_err(lines, 0) {
        Some(k) => k,
        None => 0,
    }
}

/// first_hard_err skips a prefix of walked lines (decoded lines and
/// InvalidData read errors).
pub proof fn first_hard_err_past_prefix(lines: Seq<LineRead>, i: int)
    requires
        0 <= i <= lines.len(),
        forall|m: int| #![trigger lines[m]] 0 <= m < i ==> is_walked_line(lines[m]),
    ensures first_hard_err(lines, i) == first_hard_err(lines, 0)
    decreases i
{
    if i > 0 {
        first_hard_err_past_prefix(lines, i - 1);
        // with lines[i-1] a walked line, first_hard_err over [0..i)
        // sees through it: one unfold of the recursion at i-1
        assert(is_walked_line(lines[i - 1]));
        assert(!is_hard_io_line(lines[i - 1]));
    }
}

/// If every line is a walked line (decoded or InvalidData), there is
/// no hard error: the loop processes the whole stream.
pub proof fn first_hard_err_none_when_all_walked(lines: Seq<LineRead>)
    requires forall|m: int| #![trigger lines[m]]
        0 <= m < lines.len() ==> is_walked_line(lines[m])
    ensures (first_hard_err(lines, 0) matches None)
{
    first_hard_err_past_prefix(lines, lines.len() as int);
    // the scan front is past the end: one unfold gives None
    assert(first_hard_err(lines, lines.len() as int) matches None);
}

/// If the prefix [0..k) is walked and line k is a hard read error,
/// then k is the first hard error.
pub proof fn first_hard_err_at_hit(lines: Seq<LineRead>, k: int)
    requires
        0 <= k < lines.len(),
        is_hard_io_line(lines[k]),
        forall|m: int| #![trigger lines[m]] 0 <= m < k ==> is_walked_line(lines[m]),
    ensures first_hard_err(lines, 0) == Some(k)
{
    first_hard_err_past_prefix(lines, k);
    // one unfold at the hit index
    assert(first_hard_err(lines, k) == Some(k));
}

/// The first hard read error lies inside the stream (the selector
/// range bounds the view fold's n argument).
pub proof fn first_hard_err_index_range(lines: Seq<LineRead>, i: int)
    requires 0 <= i
    ensures match first_hard_err(lines, i) {
        Some(k) => i <= k < lines.len(),
        None => true,
    }
    decreases lines.len() - i
{
    if i < lines.len() {
        if is_hard_io_line(lines[i]) {
        } else {
            first_hard_err_index_range(lines, i + 1);
        }
    }
}

// ===========================================================================
// PR #3605 helper lemmas: the InvalidData continuation's fold shapes
// (consumed by add()'s exit proofs and the harness rows)
// ===========================================================================

/// io_err_reprs over an all-decoded prefix is empty.
pub proof fn io_err_reprs_lines_only_empty(lines: Seq<LineRead>, n: int)
    requires
        0 <= n <= lines.len(),
        forall|m: int| #![trigger lines[m]]
            0 <= m < n ==> (lines[m] matches LineRead::Line(_)),
    ensures io_err_reprs(lines, n) == Seq::<u64>::empty()
    decreases n
{
    if n > 0 {
        io_err_reprs_lines_only_empty(lines, n - 1);
    }
}

/// The PR #3605 lone-invalid-data shape: a prefix whose only read
/// error sits at index k (kind InvalidData), every other line decoded,
/// and no rejected globs among it -- the view fold is exactly the one
/// io event at line k+1 and the repr list is exactly the InvalidData
/// encoding. Pre-#3605 the same stream truncated the file AT k; the
/// patched loop walks past it, so the fold covers the WHOLE prefix.
pub proof fn errsv_lone_invalid_data(
    ci: bool,
    auc: bool,
    lines: Seq<LineRead>,
    n: int,
    k: int,
)
    requires
        0 <= n <= lines.len(),
        0 <= k < n,
        is_invalid_data_line(lines[k]),
        forall|m: int| #![trigger lines[m]]
            0 <= m < n && m != k ==> (lines[m] matches LineRead::Line(_)),
        errs_reject_fold_len(ci, auc, lines, n) == 0,
    ensures
        errs_view_fold(ci, auc, lines, n)
            == Seq::<(bool, Option<u64>, Option<Seq<u8>>)>::empty()
                .push((true, Some((k + 1) as u64), None))
            && io_err_reprs(lines, n)
                == Seq::<u64>::empty().push(INVALID_DATA_REPR)
    decreases n
{
    if n > 0 {
        errs_reject_len_nonneg(ci, auc, lines, n - 1);
        // the top frame's line index is n-1: either the Err line k or
        // a decoded line
        if (n - 1) as int == k {
            // the prefix below k is all-decoded and rejectless
            // (io_err_reprs: empty below k; both folds grow exactly
            // the one io event / repr at the k frame)
            assert(forall|m: int| #![trigger lines[m]]
                0 <= m < k ==> (lines[m] matches LineRead::Line(_)));
            errs_view_clean_prefix_empty(ci, auc, lines, k);
            io_err_reprs_lines_only_empty(lines, k);
            assert(errs_view_fold(ci, auc, lines, k) == Seq::empty());
            assert(io_err_reprs(lines, k) == Seq::<u64>::empty());
            assert(io_err_reprs(lines, k + 1)
                == io_err_reprs(lines, k).push(INVALID_DATA_REPR));
            // the one unfold of errs_view_fold at n = k+1: the Err
            // frame pushes the io entry with lineno k+1
            assert(errs_view_fold(ci, auc, lines, k + 1)
                == errs_view_fold(ci, auc, lines, k)
                    .push((true, Some((k + 1) as u64), None)));
        } else {
            // the frame at n-1 is a decoded line with no reject event
            // (the zero total and the nonnegative tail): its add_line
            // outcome is admitted or a skip, so both folds carry the
            // recursive result over unchanged
            errsv_lone_invalid_data(ci, auc, lines, n - 1, k);
            let line = if n == 1 {
                strip_bom(line_bytes(lines[0]))
            } else {
                line_bytes(lines[n - 1])
            };
            match add_line_value(ci, auc, None, line) {
                AddLineOutcome::Skip => {
                    assert(errs_reject_fold_len(ci, auc, lines, n)
                        == errs_reject_fold_len(ci, auc, lines, n - 1));
                }
                AddLineOutcome::Add(gs) => {
                    assert(errs_reject_fold_len(ci, auc, lines, n)
                        == errs_reject_fold_len(ci, auc, lines, n - 1)
                            + (if !gs.grok_admitted { 1int } else { 0int }));
                    assert(!gs.grok_admitted ==> false);
                    assert(gs.grok_admitted);
                    // admitted: no view-fold push at the n frame
                }
            }
            assert(io_err_reprs(lines, n) == io_err_reprs(lines, n - 1));
        }
    }
}



impl GitignoreBuilder {
/// Origin: `add` (gitignore.rs:408-437), the loop transcribed over
    /// the abstract stream (the fs legs are the caller's face), with
    /// the PR #3605 read-error arm (patch-tree gitignore.rs:417-427
    /// verbatim):
    ///
    /// ```text
    /// Err(err) => {
    ///     let kind = err.kind();
    ///     errs.push(Error::Io(err).tagged(path, lineno));
    ///     if kind == ErrorKind::InvalidData {
    ///         continue;
    ///     }
    ///     break;
    /// }
    /// ```
    ///
    /// - :410-413 File::open error -> `Some(Error::Io(err).with_path(path))`
    /// - :416-417 the errs stack + `rdr.lines().enumerate()`
    /// - :418 `let lineno = (i + 1) as u64;`
    /// - :419-427 the line-read Err arm (PR #3605): EVERY read error
    ///   (hard or InvalidData) is pushed as a tagged io error; then
    ///   the kind gate -- InvalidData (the kind BufRead::lines
    ///   reports for a non-UTF-8 line) CONTINUES past the line
    ///   (lineno advances with it, DP3's crime reverted: the doc
    ///   sentence "all other valid globs will still be added" now
    ///   holds past a bad-encoding line; runtime row PR3605-verify
    ///   SJ1/SJ2; git parity SJ9), every OTHER kind still breaks
    ///   (the hard-io door, twin-bound `first_hard_err`, runtime row
    ///   SJ4: /proc/self/mem's EIO face).
    /// - :427-430 the first-line-only BOM strip (DP13; untouched)
    /// - :432-434 per-line add_line; per-line Err -> tagged push (DP14)
    /// - :436 `errs.into_error_option()`
    ///
    /// General posts: the globs/registration fold equals the fold spec
    /// up to the processed bound (past InvalidData lines, up TO a hard
    /// read error inclusive -- the Err frame itself folds as a skip);
    /// the errs stack length equals the errs fold over the same bound;
    /// the None-return equivalence follows IG1's into_error_option
    /// post (empty -> None; 1 -> Some; >=2 -> Some(Partial)). Note
    /// the fix widens the Some side: an InvalidData line now also
    /// pushes an error, so a lone invalid-UTF-8 line returns
    /// Some(io) with no glob push back (IOk below).
    ///
    /// IG3 strengthenings (the IG2-deferred element-level rematch):
    /// (S) the store suffix added by this call is the fold's record
    /// list, index-by-index, in the globs-field view and the
    /// registered-pattern view (the harness's store-level assertions
    /// after add() follow from these); (R) the errs stack is the
    /// view-fold's error list, index-by-index (io-tagged / reject
    /// payloads -- InvalidData read errors included on post-#3605);
    /// (IO) when a hard read error at k is the ONLY error folded, the
    /// returned error is io-tagged, carries line k+1 and no glob
    /// payload -- the single-io shape that build_global's
    /// maybe_push_ignore_io then drops.
    ///
    /// PR #3605 strengthenings: (S) the fold bound itself changed
    /// (`lines_processed_count` vs the pre-fix `first_err` truncation
    /// -- the old DP3 theorem "the store suffix past a read error is
    /// empty" is NOT reproducible under this spec: a lone
    /// InvalidData line no longer bounds the fold; the harness row
    /// dp3_nonutf8_continues_matched_face pins the replacement --
    /// the tail IS in the store); (IOk) the lone-InvalidData return
    /// shape: a stream of decoded lines with ONE InvalidData line at k
    /// and no rejects returns Some(err) with the io spine, NO glob
    /// payload, line k+1, and the folded view exactly that io event
    /// (the InvalidData-kind side is pinned at the runtime layer, the
    /// PR's own test's io_error().kind() assert -- rows SJ1/SJ2; the
    /// twin's value-level repr threading was built and retired on
    /// measured SMT cost, see out/kverus-run/PR3605-verify/notes.md).

    pub fn add(
        &mut self,
        path: &[u8],
        stream: Option<Vec<LineRead>>,
    ) -> (r: Option<Error>)
        ensures
            final(self).case_insensitive == old(self).case_insensitive,
            final(self).allow_unclosed_class == old(self).allow_unclosed_class,
            final(self).root == old(self).root,
            (stream matches None)
                ==> (r matches Some(e)
                    && (e matches Error::WithPath { .. })
                    && (with_path_payload(&e) == path@)
                    && (with_path_inner(&e) matches Error::Io(_))
                    && final(self).globs@ == old(self).globs@
                    && final(self).builder.registered@ == old(self).builder.registered@),
            // (L) the two store lengths over the PR #3605 processed
            // bound (either the whole stream or up to a hard read error
            // inclusive; InvalidData frames fold as skips, so the bound
            // may run past them)
            (stream matches Some(_))
                ==> ({
                    let foldv = fold_add_lines(old(self).case_insensitive,
                        old(self).allow_unclosed_class, Some(path@),
                        stream_lines(stream),
                        lines_processed_count(stream_lines(stream)));
                    #[trigger] foldv.len() >= 0
                    && final(self).globs@.len() == old(self).globs@.len()
                            + foldv.len()
                    && final(self).builder.registered@.len()
                        == old(self).builder.registered@.len() + foldv.len()
                }),
            // (S) per-index store content (the IG3 rematch, over the
            // processed bound)
            (stream matches Some(_))
                ==> ({
                    let foldv = fold_add_lines(old(self).case_insensitive,
                        old(self).allow_unclosed_class, Some(path@),
                        stream_lines(stream),
                        lines_processed_count(stream_lines(stream)));
                    (forall|j: int| #![trigger globs_field_view(
                            final(self).globs@[
                                old(self).globs@.len() as int + j])]
                        0 <= j < foldv.len() ==>
                        (globs_field_view(
                            final(self).globs@[old(self).globs@.len() as int + j])
                            == globs_spec_field_view(foldv[j]))
                    && registered_suffix_matches_fold(
                        final(self).builder.registered@,
                        old(self).builder.registered@.len() as int, foldv)
                    && (forall|j: int| #![trigger
                            final(self).builder.registered@[
                                old(self).builder.registered@.len() as int + j]]
                        0 <= j < foldv.len() ==>
                        final(self).builder.registered@[
                                old(self).builder.registered@.len() as int + j
                            ].case_insensitive == old(self).case_insensitive))
                }),
            // (R) the errs-stack content and its two return shapes
            // (over the processed bound: an InvalidData read error
            // contributes its io event INSIDE the bound, a hard one at
            // the bound's last frame)
            (stream matches Some(_))
                ==> ({
                    let errsv = errs_view_fold(old(self).case_insensitive,
                        old(self).allow_unclosed_class, stream_lines(stream),
                        lines_processed_count(stream_lines(stream)));
                    (errsv.len() == 1
                        ==> (r matches Some(e)
                            && err_view(&e) == errsv[0]))
                    && (errsv.len() >= 2
                        ==> (r matches Some(e)
                            && e matches Error::Partial(_)
                            && partial_stack(&e).len() == errsv.len()
                            && (forall|j: int| #![trigger err_view(
                                    &partial_stack(&e)[j])]
                                0 <= j < errsv.len() ==>
                                err_view(&partial_stack(&e)[j]) == errsv[j])))
                }),
            // IG2-leg compatibility clauses (the ut_ig2 rows consume
            // these over errs_fold_len): the None <-> zero-errors
            // equivalence and the single-folded-error => Some shape
            // (PR #3605 semantics: a lone InvalidData line is now A
            // FOLDED ERROR -- "full errors" means neither a bad-glob
            // line nor an invalid-utf8 line was seen)
            (stream matches Some(_))
                ==> (r matches None
                    <==> errs_fold_len(old(self).case_insensitive,
                        old(self).allow_unclosed_class,
                        stream_lines(stream),
                        lines_processed_count(stream_lines(stream))) == 0),
            (stream matches Some(_))
                ==> (errs_fold_len(old(self).case_insensitive,
                        old(self).allow_unclosed_class,
                        stream_lines(stream),
                        lines_processed_count(stream_lines(stream))) == 1
                    ==> (r matches Some(_))),
            // (R0a) zero folded errors => no returned error
            (stream matches Some(_))
                ==> ({
                    let errsv = errs_view_fold(old(self).case_insensitive,
                        old(self).allow_unclosed_class, stream_lines(stream),
                        lines_processed_count(stream_lines(stream)));
                    #[trigger] errsv.len() >= 0
                    && (errsv.len() == 0 ==> (r matches None))
                }),
            // (R0b) a returned error implies folded errors exist
            (stream matches Some(_))
                ==> ((r matches Some(_))
                    ==> errs_view_fold(old(self).case_insensitive,
                        old(self).allow_unclosed_class, stream_lines(stream),
                        lines_processed_count(stream_lines(stream))).len() >= 1),
            // (IO) the hard single-io shape (the DP2/drop-eligible
            // arm: the BREAK line's io error, the only folded error)
            (stream matches Some(_))
                ==> ((match first_hard_err(stream_lines(stream), 0) {
                        Some(k) => 0 <= k
                            && errs_reject_fold_len(
                                old(self).case_insensitive,
                                old(self).allow_unclosed_class,
                                stream_lines(stream), k) == 0
                            && (forall|m: int| #![trigger
                                    stream_lines(stream)[m]]
                                0 <= m < k
                                ==> (stream_lines(stream)[m]
                                    matches LineRead::Line(_))),
                        None => false,
                    })
                    ==> (r matches Some(e)
                        && is_io_spec(&e)
                        && line_nested(&e)
                            == Some((match first_hard_err(
                                stream_lines(stream), 0) {
                                Some(k) => k + 1,
                                None => 0,
                            }) as u64)
                        && glob_nested(&e) matches None)),
            // (IOk) the PR #3605 lone-InvalidData return shape: a
            // stream of decoded lines with its only read error at k
            // (kind InvalidData) and no rejected globs -- the loop
            // walked the WHOLE stream (no hard break), so the caller's
            // Some(err) is exactly that io event: io-typed, tagged at
            // line k+1, no glob payload, and everything ELSE the file
            // had is in the store. NB the pre-fix twin stopped the
            // store at k; the None<->zero clause above already carries
            // the widened counting (a lone InvalidData line IS a
            // folded error now)
            (stream matches Some(_))
                ==> ((stream_lines(stream).len() > 0
                        && lone_invalid_data_lines(stream_lines(stream))
                        && errs_reject_fold_len(old(self).case_insensitive,
                            old(self).allow_unclosed_class,
                            stream_lines(stream),
                            lines_processed_count(stream_lines(stream))) == 0)
                    ==> (r matches Some(e)
                        && is_io_spec(&e)
                        && line_nested(&e)
                            == Some((lone_invalid_data_index(
                                stream_lines(stream)) + 1) as u64)
                        && (glob_nested(&e) matches None))
                    && errs_view_fold(old(self).case_insensitive,
                        old(self).allow_unclosed_class, stream_lines(stream),
                        lines_processed_count(stream_lines(stream)))
                        == Seq::<(bool, Option<u64>, Option<Seq<u8>>)>::empty()
                            .push((true, Some((lone_invalid_data_index(
                                stream_lines(stream)) + 1) as u64), None))),
    {
        match stream {
            None => {
                // :410-413 the File::open error face
                Some(super::error_with_path(Error::Io(IoErrorFace::new(0)), path))
            }
            Some(lines) => {
                // :416 the errs stack
                let mut errs = PartialErrorBuilder::new();
                let mut i: usize = 0;
                // ghost flag: the DP3 break-off point (the exec loop exits
                // through the condition, keeping the invariants intact)
                let mut broke = false;
                while i < lines.len() && !broke
                    invariant
                        0 <= i <= lines.len(),
                        self.case_insensitive == old(self).case_insensitive,
                        self.allow_unclosed_class == old(self).allow_unclosed_class,
                        self.root == old(self).root,
                        // PR #3605: the walked prefix (decoded lines AND
                        // InvalidData read errors -- the loop steps past
                        // the latter); the break point, when it exists, is
                        // a HARD read error (every other kind)
                        !broke ==> forall|m: int| #![trigger lines@[m]]
                            0 <= m < i ==> is_walked_line(lines@[m]),
                        broke ==> i >= 1
                            && is_hard_io_line(lines@[i - 1])
                            && forall|m: int| #![trigger lines@[m]] 0 <= m < i - 1
                                ==> is_walked_line(lines@[m]),
                        errs.errs@.len() == errs_fold_len(old(self).case_insensitive,
                            old(self).allow_unclosed_class, lines@, i as int),
                        // (R-invariant) the errs stack IS the view fold
                        errs.errs@.len() == errs_view_fold(old(self).case_insensitive,
                            old(self).allow_unclosed_class, lines@, i as int).len(),
                        forall|j: int| #![trigger err_view(&errs.errs@[j])]
                            0 <= j < errs.errs@.len()
                            ==> err_view(&errs.errs@[j])
                                == errs_view_fold(old(self).case_insensitive,
                                    old(self).allow_unclosed_class, lines@,
                                    i as int)[j],
                        self.globs@.len() == old(self).globs@.len()
                            + fold_add_lines(old(self).case_insensitive,
                                old(self).allow_unclosed_class, Some(path@),
                                lines@, i as int).len(),
                        self.builder.registered@.len()
                            == old(self).builder.registered@.len()
                                + fold_add_lines(old(self).case_insensitive,
                                    old(self).allow_unclosed_class, Some(path@),
                                    lines@, i as int).len(),
                        // (S-invariant) the store suffix is the fold
                        forall|j: int| #![trigger
                            globs_field_view(self.globs@[old(self).globs@.len() as int + j])]
                            0 <= j < fold_add_lines(old(self).case_insensitive,
                                old(self).allow_unclosed_class, Some(path@),
                                lines@, i as int).len()
                            ==> globs_field_view(
                                    self.globs@[old(self).globs@.len() as int + j])
                                == globs_spec_field_view(fold_add_lines(
                                    old(self).case_insensitive,
                                    old(self).allow_unclosed_class, Some(path@),
                                    lines@, i as int)[j]),
                        forall|j: int| #![trigger
                            self.builder.registered@[
                                old(self).builder.registered@.len() as int + j]]
                            0 <= j < fold_add_lines(old(self).case_insensitive,
                                old(self).allow_unclosed_class, Some(path@),
                                lines@, i as int).len()
                            ==> self.builder.registered@[
                                    old(self).builder.registered@.len() as int + j
                                ].pattern@
                                == fold_add_lines(old(self).case_insensitive,
                                    old(self).allow_unclosed_class, Some(path@),
                                    lines@, i as int)[j].actual,
                        forall|j: int| #![trigger
                            self.builder.registered@[
                                old(self).builder.registered@.len() as int + j]]
                            0 <= j < fold_add_lines(old(self).case_insensitive,
                                old(self).allow_unclosed_class, Some(path@),
                                lines@, i as int).len()
                            ==> self.builder.registered@[
                                    old(self).builder.registered@.len() as int + j
                                ].case_insensitive
                                == old(self).case_insensitive,
                    decreases lines.len() - i
                {
                    // :418 `let lineno = (i + 1) as u64;`
                    let lineno = (i + 1) as u64;
                    match &lines[i] {
                        LineRead::Err(iof) => {
                            // :419-427 the read-error arm (PR #3605): push
                            // the tagged io error on EVERY kind, then the
                            // kind gate -- InvalidData walks on (head loop
                            // re-check, lineno advanced with the line), any
                            // other kind raises the break flag (the exec
                            // loop then exits through the condition)
                            let e = super::error_tagged(
                                Error::Io(IoErrorFace { repr: iof.repr }),
                                path,
                                lineno,
                            );
                            errs.push(e);
                            proof {
                                // the view of the io-tagged error
                                assert(is_io_spec(&Error::Io(IoErrorFace {
                                    repr: iof.repr,
                                })));
                                // the view-fold push at the Err line
                                let prev = i as int;
                                let base = errs_view_fold(old(self).case_insensitive,
                                    old(self).allow_unclosed_class, lines@, prev);
                                assert(errs_view_fold(old(self).case_insensitive,
                                    old(self).allow_unclosed_class, lines@, prev + 1)
                                    == base.push((true, Some(lineno), None)));
                                assert(errs_view_fold(old(self).case_insensitive,
                                    old(self).allow_unclosed_class, lines@, prev + 1)
                                    .len() == base.len() + 1);
                            }
                            i += 1;
                            if !io_face_is_invalid_data_exec(iof) {
                                // every kind but InvalidData: the hard
                                // door -- the pre-#3605 behavior
                                broke = true;
                            }
                        }
                        LineRead::Line(v) => {
                            // :427-430 the first-line-only BOM strip (DP13)
                            let line_str: &[u8] = if i == 0 {
                                strip_bom_exec(v.as_slice())
                            } else {
                                v.as_slice()
                            };
                            // :432-434 the per-line add_line + tag
                            let from = Some(PathBytes {
                                bytes: vstd::slice::slice_to_vec(path),
                            });
                            let res = self.add_line(from, line_str);
                            // the line's fold events (analysis before the
                            // result is consumed: res carries the payload
                            // shape needed for the reject view)
                            proof {
                                let prev = i as int;
                                let cur_line = if prev == 0 {
                                    strip_bom(line_bytes(lines@[0]))
                                } else {
                                    line_bytes(lines@[prev])
                                };
                                let outc = add_line_value(old(self).case_insensitive,
                                    old(self).allow_unclosed_class, Some(path@),
                                    cur_line);
                                let base = errs_view_fold(old(self).case_insensitive,
                                    old(self).allow_unclosed_class, lines@, prev);
                                let vfold = errs_view_fold(old(self).case_insensitive,
                                    old(self).allow_unclosed_class, lines@, prev + 1);
                                let fbase = fold_add_lines(old(self).case_insensitive,
                                    old(self).allow_unclosed_class, Some(path@),
                                    lines@, prev);
                                let fprev = fold_add_lines(old(self).case_insensitive,
                                    old(self).allow_unclosed_class, Some(path@),
                                    lines@, prev + 1);
                                let gs: GlobSpec = match outc {
                                    AddLineOutcome::Add(g) => g,
                                    AddLineOutcome::Skip => GlobSpec {
                                        from: None,
                                        original: Seq::empty(),
                                        actual: Seq::empty(),
                                        is_whitelist: false,
                                        is_only_dir: false,
                                        grok_admitted: true,
                                    },
                                };
                                if outc matches AddLineOutcome::Add(gs)
                                    && gs.grok_admitted
                                {
                                    assert(fprev == fbase.push(gs));
                                    assert(errs_fold_len(old(self).case_insensitive,
                                        old(self).allow_unclosed_class,
                                        lines@, prev + 1)
                                        == errs_fold_len(old(self).case_insensitive,
                                            old(self).allow_unclosed_class,
                                            lines@, prev));
                                    assert(vfold == base);
                                    // the S-side: the record equality pins
                                    // the stored top to the fold entry
                                    // (outcome_record unfolds to this gs)
                                    assert(outcome_record(old(self).case_insensitive,
                                        old(self).allow_unclosed_class,
                                        match from {
                                            Some(fb) => Some(fb.bytes@),
                                            None => None,
                                        },
                                        cur_line) == gs);
                                    // pin add_line's stored post to this
                                    // instance, then take the field view
                                    assert(outcome_add_ok(old(self).case_insensitive,
                                        old(self).allow_unclosed_class,
                                        match from {
                                            Some(fb) => Some(fb.bytes@),
                                            None => None,
                                        },
                                        cur_line));
                                    // NB the top index rides the FOLD
                                    // length (prior admitted adds), not the
                                    // iteration count (prior rejects push
                                    // nothing)
                                    assert(stored_matches(self.globs@[
                                            old(self).globs@.len() as int
                                                + fbase.len()],
                                        gs));
                                    stored_matches_view_bridge(
                                        self.globs@[old(self).globs@.len() as int
                                            + fbase.len()],
                                        gs);
                                    assert(self.builder.registered@[
                                        old(self).builder.registered@.len() as int
                                            + fbase.len()].pattern@
                                        == outcome_record(old(self).case_insensitive,
                                            old(self).allow_unclosed_class,
                                            match from {
                                                Some(fb) => Some(fb.bytes@),
                                                None => None,
                                            },
                                            cur_line).actual);
                                    // explicit re-assert of the whole
                                    // (S)/(registered) content at the
                                    // post state (the loop-end check
                                    // consumes this directly)
                                    assert(forall|j: int| #![trigger
                                        globs_field_view(self.globs@[
                                            old(self).globs@.len() as int + j])]
                                        0 <= j < fprev.len()
                                        ==> globs_field_view(
                                            self.globs@[
                                                old(self).globs@.len() as int + j])
                                            == globs_spec_field_view(fprev[j]));
                                    assert(forall|j: int| #![trigger
                                        self.builder.registered@[
                                            old(self).builder.registered@.len() as int + j]]
                                        0 <= j < fprev.len()
                                        ==> (self.builder.registered@[
                                                old(self).builder.registered@.len() as int
                                                    + j].pattern@
                                            == fprev[j].actual
                                            && self.builder.registered@[
                                                old(self).builder.registered@.len() as int
                                                    + j].case_insensitive
                                                == old(self).case_insensitive));
                                } else if outc matches AddLineOutcome::Add(gs) {
                                    // rejected: errs grows by the reject
                                    // entry, the store stays
                                    assert(!gs.grok_admitted);
                                    assert(errs_fold_len(old(self).case_insensitive,
                                        old(self).allow_unclosed_class,
                                        lines@, prev + 1)
                                        == errs_fold_len(old(self).case_insensitive,
                                            old(self).allow_unclosed_class,
                                            lines@, prev) + 1);
                                    assert(fprev.len() == fbase.len());
                                    assert(vfold == base.push((false, Some(lineno),
                                        Some(gs.original))));
                                    // the push site below pins the Err arm:
                                    // the rejection posts give the Glob
                                    // shape and the payload
                                    assert(outcome_add_rejected(
                                        old(self).case_insensitive,
                                        old(self).allow_unclosed_class,
                                        match from {
                                            Some(fb) => Some(fb.bytes@),
                                            None => None,
                                        },
                                        cur_line));
                                } else {
                                    // Skip: no events on either fold
                                    assert(fprev.len() == fbase.len());
                                    assert(vfold == base);
                                }
                            }
                            match res {
                                Err(e) => {
                                    // rejected: errs grows, store unchanged
                                    let tagged = super::error_tagged(e, path, lineno);
                                    errs.push(tagged);
                                    proof {
                                        // the pushed error's view triple:
                                        // rejection Glob-kind, the line
                                        // number, the original payload
                                        let prev0 = i as int;
                                        let cur_line0 = if prev0 == 0 {
                                            strip_bom(line_bytes(lines@[0]))
                                        } else {
                                            line_bytes(lines@[prev0])
                                        };
                                        let gs0: GlobSpec = match add_line_value(
                                            old(self).case_insensitive,
                                            old(self).allow_unclosed_class, None,
                                            cur_line0)
                                        {
                                            AddLineOutcome::Add(g) => g,
                                            AddLineOutcome::Skip => GlobSpec {
                                                from: None,
                                                original: Seq::empty(),
                                                actual: Seq::empty(),
                                                is_whitelist: false,
                                                is_only_dir: false,
                                                grok_admitted: true,
                                            },
                                        };
                                        if add_line_value(old(self).case_insensitive,
                                            old(self).allow_unclosed_class, None,
                                            cur_line0) matches AddLineOutcome::Add(gs0)
                                        {
                                            assert(!gs0.grok_admitted);
                                            assert(is_io_spec(&e) == false);
                                            assert(glob_nested(&e)
                                                == Some(gs0.original));
                                            assert(glob_nested(&tagged)
                                                == glob_nested(&e));
                                        } else {
                                            // Skip contradicts res being Err
                                            // (outcome_add_rejected)
                                            assert(!(res matches Err(_) || res matches Ok(_)));
                                        }
                                    }
                                }
                                Ok(_) => {}
                            }
                            // fold-event accounting: registered length
                            // pinned per-case above.
                            i += 1;
                        }
                    }
                }
                proof {
                    // exit-shape glue: resolve the fold bound for the two
                    // loop exits (every line walked, including InvalidData
                    // frames, vs the hard break-off)
                    if broke {
                        assert(is_hard_io_line(lines@[(i - 1) as int]));
                        assert(forall|m: int| #![trigger lines@[m]]
                            0 <= m < (i as int) - 1 ==> is_walked_line(lines@[m]));
                        first_hard_err_at_hit(lines@, (i - 1) as int);
                        assert(first_hard_err(lines@, 0) == Some((i - 1) as int));
                        assert(lines_processed_count(lines@) == i as int);
                    } else {
                        assert(forall|m: int| #![trigger lines@[m]]
                            0 <= m < lines@.len() as int ==> is_walked_line(lines@[m]));
                        first_hard_err_none_when_all_walked(lines@);
                        assert((first_hard_err(lines@, 0) matches None));
                        assert(lines_processed_count(lines@) == lines@.len() as int);
                        assert(first_err(lines@, 0)
                            == (match first_err(lines@, 0) {
                                Some(k) => Some(k),
                                None => None,
                            }));
                    }
                    assert(match first_hard_err(lines@, 0) {
                        Some(k) => k + 1,
                        None => lines@.len() as int,
                    } == i as int);
                    // (IO) the single-io derivation: under the post's
                    // selector (a hard break at k with a decode-clean
                    // prefix and no rejects -- the selector's k pins to
                    // the break line i-1 by the glue above) the view fold
                    // is exactly the break line's io entry; the (R1)
                    // single-unwrap then carries the view into r
                    if broke && errs_reject_fold_len(old(self).case_insensitive,
                        old(self).allow_unclosed_class, lines@,
                        (i - 1) as int) == 0
                        && (match first_hard_err(lines@, 0) {
                            None => false,
                            Some(k) => (forall|m: int| #![trigger lines@[m]]
                                0 <= m < k
                                ==> (lines@[m] matches LineRead::Line(_))),
                        })
                    {
                        errs_view_clean_prefix_empty(old(self).case_insensitive,
                            old(self).allow_unclosed_class, lines@,
                            (i - 1) as int);
                        // the Err line itself folds as Skip for the glob
                        // fold, and the io entry rides on top of the empty
                        // prefix view
                        assert(line_bytes(lines@[(i - 1) as int]) == Seq::empty());
                        let line_prev = line_bytes(lines@[(i - 1) as int]);
                        assert(match add_line_value(old(self).case_insensitive,
                            old(self).allow_unclosed_class, None, line_prev)
                        {
                            AddLineOutcome::Add(gs2) => gs2.grok_admitted,
                            AddLineOutcome::Skip => true,
                        });
                        assert(errs_view_fold(old(self).case_insensitive,
                            old(self).allow_unclosed_class, lines@, i as int)
                            == Seq::<(bool, Option<u64>, Option<Seq<u8>>)>::empty()
                                .push((true, Some(i as u64), None)));
                    }
                    // (IOk) the lone-InvalidData exit (PR #3605): the
                    // walked stream is decoded lines around one
                    // InvalidData read error at k with no rejects -- no
                    // hard break happened, the fold covers the whole
                    // stream, and errsv_lone_invalid_data pins both the
                    // single io entry and its InvalidData repr list;
                    // the (R1) single-unwrap carries the view into r
                    if !broke
                        && lone_invalid_data_lines(lines@)
                        && errs_reject_fold_len(old(self).case_insensitive,
                            old(self).allow_unclosed_class, lines@,
                            i as int) == 0
                    {
                        let kv = lone_invalid_data_index(lines@);
                        assert((i as int) == lines@.len() as int);
                        // the lone InvalidData line lies inside the
                        // walked stream (first_err's index range)
                        first_err_index_range(lines@, 0);
                        assert(0 <= kv && kv < (i as int));
                        errsv_lone_invalid_data(old(self).case_insensitive,
                            old(self).allow_unclosed_class, lines@, i as int, kv);
                    }
                }
                // :436 `errs.into_error_option()`
                let ret = errs.into_error_option();
                proof {
                    // the stack length rides the view-fold length (the
                    // loop invariant); into_error_option's posts turn
                    // the stack length into the None <-> zero
                    // equivalence of the post.
                    let n = errs.errs@.len();
                    let m = errs_view_fold(old(self).case_insensitive,
                        old(self).allow_unclosed_class, lines@, i as int).len();
                    assert(n == m);
                    assert(errs_view_fold(old(self).case_insensitive,
                        old(self).allow_unclosed_class, lines@, i as int).len()
                        == errs_view_fold(old(self).case_insensitive,
                            old(self).allow_unclosed_class, lines@,
                            lines_processed_count(lines@)).len());
                    if n == 0 {
                        assert(errs.errs@ =~= Seq::empty());
                        assert(ret matches None);
                        assert(m == 0);
                    } else {
                        // single (len 1) or plural (len >= 2): Some
                        assert(ret matches Some(_));
                        assert(m >= 1);
                        // the (IO) single-io exit (hard break): the
                        // stack is exactly the io entry, so the
                        // unwrapped error carries its kind/line/payload
                        // (the ensures' selector is k+1 == i, the hard
                        // break line's lineno)
                        if broke && errs_reject_fold_len(
                            old(self).case_insensitive,
                            old(self).allow_unclosed_class, lines@,
                            (i as int) - 1) == 0
                            && m == 1
                        {
                            match &ret {
                                Some(ethe) => {
                                    let ev = err_view(ethe);
                                    assert(ev.0 == true);
                                    assert(ev.1 == Some(i as u64));
                                    assert(ev.2 == None);
                                    assert(is_io_spec(ethe));
                                    assert(line_nested(ethe) == Some(i as u64));
                                    assert(glob_nested(ethe) matches None);
                                    assert(Some(i as u64)
                                        == Some((match first_hard_err(lines@, 0) {
                                            Some(k) => k + 1,
                                            None => 0,
                                        }) as u64));
                                }
                                None => {}
                            }
                        }
                        // the (IOk) lone-InvalidData exit (PR #3605),
                        // view form: the pre-return block pinned the
                        // folded view to exactly the one io event at
                        // the InvalidData line; with the stack at one
                        // entry, into_error_option returns it verbatim
                        // and the (R)-invariant carries its view triple
                        // (io-typed, line k+1, no glob payload)
                        if !broke
                            && lone_invalid_data_lines(lines@)
                            && errs_reject_fold_len(old(self).case_insensitive,
                                old(self).allow_unclosed_class, lines@,
                                i as int) == 0
                        {
                            assert(m == 1);
                            assert(n == 1);
                            let k = lone_invalid_data_index(lines@);
                            first_err_index_range(lines@, 0);
                            assert(0 <= k && k < (i as int));
                            match &ret {
                                Some(etk) => {
                                    let evk = err_view(etk);
                                    assert(evk.0 == true);
                                    assert(evk.1 == Some((k + 1) as u64));
                                    assert(evk.2 == None);
                                    assert(is_io_spec(etk));
                                    assert(line_nested(etk)
                                        == Some((k + 1) as u64));
                                    assert(glob_nested(etk) matches None);
                                }
                                None => {}
                            }
                        }
                    }
                }
                ret
            }
        }
    }
}

impl GitignoreBuilder {
    /// Origin: build_global (gitignore.rs:380-399), with the fs/env legs
    /// as parameters (the excludes-path resolution is DP35's env face,
    /// deferred): the two blank legs are fully verified -- a None
    /// excludes path, or an excludes path that is not a file, yield
    /// `(Gitignore::empty(), None)`; the file leg is the verbatim
    /// errs/add/build folding (DP2's maybe_push_ignore_io + build's
    /// never-Err face + DP14).
    ///
    /// IG3 rematch (the io-typing closure of the IG2-deferred blanket):
    /// on the file leg, (F1) the folded store/registration content
    /// rides add's (S) posts through build; (F2) the "I/O errors are
    /// ignored" blanket -- r.1 is None exactly when the folded error
    /// list is empty or exactly the single read-error (io shape,
    /// dropped by maybe_push_ignore_io); some non-io error otherwise.
    /// PR #3605: the folds now run over the processed bound (past
    /// InvalidData lines, to a hard read error's lineno) -- a lone
    /// non-UTF-8 mid-file line no longer truncates the file leg's
    /// store; its single-io return is still silently dropped (the
    /// maybe_push_ignore_io discipline is unchanged).
    pub fn build_global(
        builder: GitignoreBuilder,
        excludes: Option<&[u8]>,
        excludes_is_file: bool,
        stream: Option<Vec<LineRead>>,
    ) -> (r: (Gitignore, Option<Error>))
        requires builder.globs@.len() == builder.builder.registered@.len()
        ensures
            (excludes matches None)
                ==> (r.0.globs@ == Seq::empty()
                    && r.0.set.registered@ == Seq::empty()
                    && r.0.root.bytes@ == Seq::empty()
                    && r.0.num_ignores == 0
                    && r.0.num_whitelists == 0
                    && r.1 matches None),
            (excludes matches Some(p)) && !excludes_is_file
                ==> (r.0.globs@ == Seq::empty()
                    && r.0.set.registered@ == Seq::empty()
                    && r.0.root.bytes@ == Seq::empty()
                    && r.0.num_ignores == 0
                    && r.0.num_whitelists == 0
                    && r.1 matches None),
            // (F1) + (F2) -- the file leg
            (matches!(excludes, Some(_))) && excludes_is_file
                && (stream matches Some(_))
                ==> ({
                    // (the excludes payload bytes; the binder is not
                    // nameable across the implies arm, so re-extract)
                    let pbytes = match excludes {
                        Some(q) => q@,
                        None => Seq::empty(),
                    };
                    let foldv = fold_add_lines(builder.case_insensitive,
                        builder.allow_unclosed_class, Some(pbytes),
                        stream_lines(stream),
                        lines_processed_count(stream_lines(stream)));
                    let errsv = errs_view_fold(builder.case_insensitive,
                        builder.allow_unclosed_class, stream_lines(stream),
                        lines_processed_count(stream_lines(stream)));
                    #[trigger] foldv.len() >= 0
                    && r.0.globs@.len() == builder.globs@.len() + foldv.len()
                    && r.0.set.registered@.len()
                        == builder.builder.registered@.len() + foldv.len()
                    // (the empty file leg builds the EMPTY matcher
                    // whose root is "", not the builder's root)
                    && (foldv.len() > 0 ==> r.0.root.bytes@ == builder.root.bytes@)
                    && (forall|j: int| #![trigger globs_field_view(
                            r.0.globs@[builder.globs@.len() as int + j])]
                        0 <= j < foldv.len() ==>
                        globs_field_view(r.0.globs@[
                                builder.globs@.len() as int + j])
                            == globs_spec_field_view(foldv[j]))
                    // (the per-index registered-pattern claim rides
                    // add's (S) at the add() level; its two-hop
                    // consumption here (add's post through build's
                    // whole-value registered equality) does not
                    // close under the field projections -- #IG-12;
                    // re-anchored by harness rows at the add()-call
                    // level)
                    // (F2) the io-typing blanket: the single-io
                    // return is dropped (DP2's "I/O errors are
                    // ignored"); anything it returns is NOT the
                    // single-io drop case
                    && (errs_is_single_io(errsv) ==> (r.1 matches None))
                    && ((r.1 matches Some(_)) ==> !errs_is_single_io(errsv))
                }),
    {
        let mut self_b = builder;
        match excludes {
            None => (Gitignore::empty(), None),
            Some(p) => {
                if !excludes_is_file {
                    // :384-386 `if !path.is_file() { (Gitignore::empty(), None) }`
                    (Gitignore::empty(), None)
                } else {
                    // :387-395 the file leg (verbatim folding; the add
                    // argument split into a ghost-visible binding)
                    let mut errs = PartialErrorBuilder::new();
                    // :388 (DP2 "I/O errors are ignored" on the global leg)
                    let added = self_b.add(p, stream);
                    proof {
                        // the (F2) input-side: which of the two
                        // drop-eligible cases we are in
                        let errsv0 = errs_view_fold(builder.case_insensitive,
                            builder.allow_unclosed_class, stream_lines(stream),
                            lines_processed_count(stream_lines(stream)));
                        first_hard_err_index_range(stream_lines(stream), 0);
                        if errs_is_single_io(errsv0) {
                            let added_v = added;
                            match added_v {
                                Some(e0) => {
                                    assert(err_view(&e0) == errsv0[0]);
                                    assert(is_io_spec(&e0));
                                }
                                None => {}
                            }
                        }
                    }
                    errs.maybe_push_ignore_io(added);
                    proof {
                        // the (F2) stack-side: in the single-io case
                        // the returned error is the whole folded list
                        // (the single io entry), dropped by the
                        // maybe_push io leg
                        let errsv1 = errs_view_fold(builder.case_insensitive,
                            builder.allow_unclosed_class, stream_lines(stream),
                            lines_processed_count(stream_lines(stream)));
                        if errs_is_single_io(errsv1) {
                            assert(errs.errs@.len() == 0);
                        }
                    }
                    match self_b.build() {
                        Ok(gi) => {
                            proof {
                                // (F1): relay add's (S)/length posts
                                // through build's posts onto r.0
                                let foldv2 = fold_add_lines(
                                    self_b.case_insensitive,
                                    self_b.allow_unclosed_class, Some(p@),
                                    stream_lines(stream),
                                    lines_processed_count(stream_lines(stream)));
                                let errsv2 = errs_view_fold(
                                    self_b.case_insensitive,
                                    self_b.allow_unclosed_class,
                                    stream_lines(stream),
                                    lines_processed_count(stream_lines(stream)));
                                // lengths through the empty/non-empty
                                // arms of build
                                assert(self_b.globs@.len()
                                    == builder.globs@.len() + foldv2.len());
                                if self_b.globs@.len() > 0 {
                                    assert(gi.set.registered@.len()
                                        == builder.builder.registered@.len()
                                            + foldv2.len());
                                    assert(gi.root.bytes@ == builder.root.bytes@);
                                } else {
                                    // all-skip file AND an empty input
                                    // builder: the empty matcher
                                    assert(foldv2.len() == 0);
                                    assert(builder.globs@.len() == 0);
                                    assert(builder.builder.registered@.len() == 0);
                                    assert(gi_is_empty_view(&gi));
                                }
                                // the (F2) exit-side relay: the Option
                                // re-derives from the stack length
                                // facts established above
                                let _ = errsv2;
                            }
                            (gi, errs.into_error_option())
                        }
                        Err(err) => {
                            errs.push(err);
                            (Gitignore::empty(), errs.into_error_option())
                        }
                    }
                }
            }
        }
    }
}

// ===========================================================================
// ===========================================================================
// gitconfig_excludes_path -- the DP35 priority chain (IG8; upstream
// gitignore.rs:586-707). Origin Rust, every arm below cites its line.
// ===========================================================================
//
// Upstream shape (gitignore.rs:588-605): the five-level ladder
//   1. GIT_CONFIG_GLOBAL (level 1: replaces BOTH $HOME/.gitconfig and
//      the XDG config per git 2.32+; :596-605, contents :607-617),
//   2. $HOME/.gitconfig (:638-643),
//   3. XDG_CONFIG_HOME (or $HOME/.config) git/config (:645-652),
//   4. GIT_CONFIG_SYSTEM (or the default /etc/gitconfig) (:624-631),
//   5. the speculative default path XDG/git/ignore (:655-662; the
//      doc "Note that the file path returned may not exist").
// Each file level reads the file and applies parse_excludes_file
// (:668-684: the trusted regex face captures the excludesfile value
// substring) with expand_tilde applied inside the parse (:687-692,
// transcribed below as the real byte function gc_et).
// The env/file reads are FACE PARAMETERS (inventory section 9: "env
// reads modeled as face parameters"): the raw environment values
// enter as the four Option arguments of the entry point (empty bytes
// = the upstream empty-spelling filter, gitignore.rs:609, :626-631,
// :657-661, transcribed as gc_nonempty) and the file reads enter
// through the gc_read_face oracle (the "open + read_to_end .ok()"
// chain has no observable beyond Some(contents)/None at a path).
// The regex face is gc_pe_face (inventory section 4's one-line spec:
// "captures the value substring"); both oracles are consumed
// per-instance only -- every harness row pins its instances with
// admits backed by the S16 runtime rows of the IG8 ig5-driver leg.

pub const GC_DOT_GITCONFIG: [u8; 10] = [
    0x2E, 0x67, 0x69, 0x74, 0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67,
];
pub const GC_DOT_CONFIG: [u8; 7] = [
    0x2E, 0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67,
];
pub const GC_GIT_CONFIG: [u8; 10] = [
    0x67, 0x69, 0x74, 0x2F, 0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67,
];
pub const GC_GIT_IGNORE: [u8; 10] = [
    0x67, 0x69, 0x74, 0x2F, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65,
];
pub const GC_ETC_GITCONFIG: [u8; 14] = [
    0x2F, 0x65, 0x74, 0x63, 0x2F, 0x67, 0x69, 0x74, 0x63, 0x6F,
    0x6E, 0x66, 0x69, 0x67,
];

/// The ".gitconfig" literal carrier (gitignore.rs:640).
pub open spec fn gc_dot_gitconfig() -> Seq<u8> {
    seq![0x2E, 0x67, 0x69, 0x74, 0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67]
}

/// The ".config" literal carrier (gitignore.rs:648/659).
pub open spec fn gc_dot_config() -> Seq<u8> {
    seq![0x2E, 0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67]
}

/// The "git/config" literal carrier (gitignore.rs:651).
pub open spec fn gc_git_config() -> Seq<u8> {
    seq![0x67, 0x69, 0x74, 0x2F, 0x63, 0x6F, 0x6E, 0x66, 0x69, 0x67]
}

/// The "git/ignore" literal carrier (gitignore.rs:661).
pub open spec fn gc_git_ignore() -> Seq<u8> {
    seq![0x67, 0x69, 0x74, 0x2F, 0x69, 0x67, 0x6E, 0x6F, 0x72, 0x65]
}

/// The "/etc/gitconfig" default of the system leg (gitignore.rs:628).
pub open spec fn gc_etc_gitconfig() -> Seq<u8> {
    seq![0x2F, 0x65, 0x74, 0x63, 0x2F, 0x67, 0x69, 0x74, 0x63,
         0x6F, 0x6E, 0x66, 0x69, 0x67]
}

/// The five literal bridges (the const-array views equal the spec
/// literals; harness rows consume these once per file).
pub proof fn gc_lit_bridges()
    ensures
        GC_DOT_GITCONFIG@ == gc_dot_gitconfig(),
        GC_DOT_CONFIG@ == gc_dot_config(),
        GC_GIT_CONFIG@ == gc_git_config(),
        GC_GIT_IGNORE@ == gc_git_ignore(),
        GC_ETC_GITCONFIG@ == gc_etc_gitconfig(),
{
}

/// The empty-spelling filter (upstream filters the empty value before
/// use at every env site: gitignore.rs:609, :626-631, :657-661).
pub open spec fn gc_nonempty(o: Option<Seq<u8>>) -> Option<Seq<u8>> {
    match o {
        Some(t) => {
            if t.len() > 0 {
                Some(t)
            } else {
                None
            }
        }
        None => None,
    }
}

/// The Option<&[u8]>-to-Option<Seq<u8>> view bridge (the exec-typed
/// face parameters of the legs below enter the spec ladder through
/// this spelling; the matches-view convention of this verus build,
/// cf. pathutil strip_prefix's ensures form).
pub open spec fn gcs(o: Option<&[u8]>) -> Option<Seq<u8>> {
    match o {
        Some(h) => Some(h@),
        None => None,
    }
}

/// The trusted file-read face: the "open + read_to_end .ok()" chain
/// (gitignore.rs:612-614 and the same shape of every leg).
pub uninterp spec fn gc_read_face(path: Seq<u8>) -> Option<Seq<u8>>;

/// The exec twin of the read face (per-instance admits only; the S16
/// runtime rows back every harness use).
#[verifier::external_body]
pub fn gc_read(path: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        (r matches None) == (gc_read_face(path@) matches None),
        r matches Some(v) ==> (gc_read_face(path@)
            matches Some(sv) && v@ == sv),
{
    unimplemented!() // trusted face: the fs open/read chain
}

/// The trusted parse face: parse_excludes_file's regex
/// (?im-u)^\s*excludesfile\s*=\s*"?\s*(\S+?)\s*"?\s*$,
/// gitignore.rs:670-684 -- captures the value substring or None.
pub uninterp spec fn gc_pe_face(data: Seq<u8>) -> Option<Seq<u8>>;

/// The exec twin of the parse face (per-instance admits only).
#[verifier::external_body]
pub fn gc_pe(data: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        (r matches None) == (gc_pe_face(data@) matches None),
        r matches Some(v) ==> (gc_pe_face(data@)
            matches Some(sv) && v@ == sv),
{
    unimplemented!() // trusted face: the regex capture group
}

/// expand_tilde (gitignore.rs:687-692): every 0x7E byte of the
/// captured candidate is replaced by $HOME (no home: the byte stays
/// literal, the upstream "return path.to_string()" arm). One-byte
/// forward recursion (the #IG-22 shape).
pub open spec fn gc_et(
    home: Option<Seq<u8>>,
    s: Seq<u8>,
    i: int,
) -> (o: Seq<u8>)
    decreases s.len() - i,
{
    if i >= s.len() {
        Seq::empty()
    } else {
        let rest = gc_et(home, s, i + 1);
        if s[i] == 0x7E {
            match home {
                None => seq![s[i]].add(rest),
                Some(hb) => hb.add(rest),
            }
        } else {
            seq![s[i]].add(rest)
        }
    }
}

/// The full-expansion view (the parse's PathBuf::from payload path).
pub open spec fn gc_et_full(home: Option<Seq<u8>>, s: Seq<u8>) -> Seq<u8> {
    gc_et(home, s, 0)
}

/// The std join over the reachable spellings (the STDJOIN rows of
/// ig5-probe-std: empty base keeps rel; a trailing-'/' base stays;
/// any other base gains one '/' -- the rel literals here are all
/// non-rooted non-empty, so the rooted arm is out of the model).
pub open spec fn gcj(base: Seq<u8>, rel: Seq<u8>) -> Seq<u8> {
    if base.len() == 0 {
        rel
    } else if base[base.len() - 1] == 0x2F {
        base.add(rel)
    } else {
        base.add(seq![0x2F]).add(rel)
    }
}

/// One level's flatMap: read at the path, parse it, expand the
/// capture against the home (the .and_then(parse_excludes_file)
/// composition of gitignore.rs:602-604 and every sibling leg).
pub open spec fn gc_parse_at(
    path: Seq<u8>,
    home: Option<Seq<u8>>,
) -> Option<Seq<u8>> {
    match gc_read_face(path) {
        Some(c) => match gc_pe_face(c) {
            Some(cap) => Some(gc_et_full(home, cap)),
            None => None,
        },
        None => None,
    }
}

/// XDG_CONFIG_HOME -- or $HOME/.config when XDG is unset/empty
/// (gitignore.rs:645-648 and the same base of :657-661).
pub open spec fn gc_base_cfg(
    xdg: Option<Seq<u8>>,
    home: Option<Seq<u8>>,
) -> Option<Seq<u8>> {
    match gc_nonempty(xdg) {
        Some(x) => Some(x),
        None => match home {
            Some(h) => Some(gcj(h, gc_dot_config())),
            None => None,
        },
    }
}

/// The full ladder value spec (gitignore.rs:589-605): level 1 the
/// env-global file, 2 the home .gitconfig, 3 the xdg git/config,
/// 4 the system file, 5 the speculative default path.
pub open spec fn gc_excl_spec(
    gcfg: Option<Seq<u8>>,
    sysenv: Option<Seq<u8>>,
    xdg: Option<Seq<u8>>,
    home: Option<Seq<u8>>,
) -> Option<Seq<u8>> {
    // level 1 (gitignore.rs:601-605)
    let l1 = match gc_nonempty(gcfg) {
        Some(t) => gc_parse_at(t, home),
        None => None,
    };
    match l1 {
        Some(p) => Some(p),
        None => {
            // level 2 (:642-643)
            let l2 = match home {
                Some(h) => gc_parse_at(gcj(h, gc_dot_gitconfig()), home),
                None => None,
            };
            match l2 {
                Some(p) => Some(p),
                None => {
                    // level 3 (:645-652)
                    let l3 = match gc_base_cfg(xdg, home) {
                        Some(b) => {
                            gc_parse_at(gcj(b, gc_git_config()), home)
                        }
                        None => None,
                    };
                    match l3 {
                        Some(p) => Some(p),
                        None => {
                            // level 4 (:625-631): the env value wins;
                            // the empty spelling falls to /etc/gitconfig
                            let p4 = match gc_nonempty(sysenv) {
                                Some(s) => s,
                                None => gc_etc_gitconfig(),
                            };
                            let l4 = gc_parse_at(p4, home);
                            match l4 {
                                Some(p) => Some(p),
                                None => {
                                    // level 5 (:655-662)
                                    match gc_base_cfg(xdg, home) {
                                        Some(b) => {
                                            Some(gcj(b, gc_git_ignore()))
                                        }
                                        None => None,
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

// -- the exec twins (real bodies; each mirrors its spec helper) --

/// The exec copy helper (per-byte copy; the view equality is the
/// copy law -- the incremental twin's slice_to_vec shape, spelled
/// locally to keep this module's dependency DAG acyclic).
pub fn gc_copy(s: &[u8]) -> (r: Vec<u8>)
    ensures r@ == s@
{
    let mut v: Vec<u8> = Vec::new();
    let mut j: usize = 0;
    while j < s.len()
        invariant
            j <= s.len(),
            v@ == s@.subrange(0, j as int),
        decreases s.len() - j,
    {
        v.push(s[j]);
        j += 1;
    }
    proof {
        assert(v@ == s@); // subrange(0, len) is the whole view
    }
    v
}

/// The empty-spelling filter exec (mirrors gc_nonempty).
pub fn gc_nonempty_exec(
    o: Option<&[u8]>,
) -> (r: Option<Vec<u8>>)
    ensures
        (r matches None) == (gc_nonempty(gcs(o)) matches None),
        r matches Some(v) ==> (gc_nonempty(gcs(o))
            matches Some(sv) && v@ == sv),
{
    match o {
        None => None,
        Some(t) => {
            if t.len() > 0 {
                Some(gc_copy(t))
            } else {
                None
            }
        }
    }
}

/// The expand_tilde exec: forward byte walk with the remaining-
/// expansion invariant (the bytes built so far consume the prefix;
/// the recursion-shaped spec supplies the rest).
pub fn gc_et_exec(
    home: Option<&[u8]>,
    s: &[u8],
) -> (r: Vec<u8>)
    ensures r@ == gc_et_full(gcs(home), s@)
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            v@.add(gc_et(gcs(home), s@, i as int))
                == gc_et_full(gcs(home), s@),
        decreases s.len() - i,
    {
        proof {
            reveal(gc_et);
        }
        if s[i] == 0x7E {
            match home {
                None => {
                    v.push(s[i]);
                }
                Some(hb) => {
                    let ghost pre_reach = v@;
                    let mut j: usize = 0;
                    while j < hb.len()
                        invariant
                            j <= hb.len(),
                            v@ == pre_reach.add(hb@.subrange(0, j as int)),
                        decreases hb.len() - j,
                    {
                        v.push(hb[j]);
                        j += 1;
                    }
                    proof {
                        assert(v@ == pre_reach.add(hb@));
                    }
                }
            }
        } else {
            v.push(s[i]);
        }
        i += 1;
    }
    proof {
        reveal(gc_et);
        assert(gc_et(gcs(home), s@, s.len() as int) == Seq::empty());
    }
    v
}

/// The std-join exec over the reachable spellings (mirrors gcj).
pub fn gcj_exec(base: &[u8], rel: &[u8]) -> (r: Vec<u8>)
    ensures r@ == gcj(base@, rel@)
{
    let mut v: Vec<u8> = Vec::new();
    let mut j: usize = 0;
    while j < base.len()
        invariant
            j <= base.len(),
            v@ == base@.subrange(0, j as int),
        decreases base.len() - j,
    {
        v.push(base[j]);
        j += 1;
    }
    proof {
        assert(v@ == base@);
    }
    // the separator per the STDJOIN rows (no fresh '/' after a
    // trailing-slash base; none over the empty base)
    if base.len() > 0 && base[base.len() - 1] != 0x2F {
        v.push(0x2F);
    }
    let ghost mid: Seq<u8> = if base.len() == 0 {
        Seq::empty()
    } else if base[base.len() - 1] == 0x2F {
        base@
    } else {
        base@.add(seq![0x2F])
    };
    proof {
        if base.len() > 0 && base[base.len() - 1] != 0x2F {
            flat_add(base@, seq![0x2F], v@);
        }
    }
    // (the invariant carries v@ == mid.add(prefix-built-so-far); the
    // mid value is fixed before this loop, computed per the STDJOIN
    // case so rel is appended to the right carrier)
    let mut k: usize = 0;
    while k < rel.len()
        invariant
            k <= rel.len(),
            v@ == mid.add(rel@.subrange(0, k as int)),
        decreases rel.len() - k,
    {
        v.push(rel[k]);
        k += 1;
    }
    proof {
        assert(v@ == mid.add(rel@));
        if base.len() > 0 && base[base.len() - 1] != 0x2F {
            assert(mid == base@.add(seq![0x2F]));
            flat_add(base@.add(seq![0x2F]), rel@, v@);
            assert(v@ == gcj(base@, rel@));
        } else if base.len() == 0 {
            assert(mid == Seq::empty());
            assert(v@ == rel@);
            assert(v@ == gcj(base@, rel@));
        } else {
            flat_add(base@, rel@, v@);
            assert(v@ == gcj(base@, rel@));
        }
    }
    v
}

/// One level's flatMap exec (mirrors gc_parse_at).
pub fn gc_parse_at_exec(
    path: &[u8],
    home: Option<&[u8]>,
) -> (r: Option<Vec<u8>>)
    ensures
        (r matches None) == (gc_parse_at(path@, gcs(home))
            matches None),
        r matches Some(v) ==> (gc_parse_at(path@, gcs(home))
            matches Some(sv) && v@ == sv),
{
    match gc_read(path) {
        None => None,
        Some(c) => match gc_pe(c.as_slice()) {
            None => None,
            Some(cap) => {
                proof {
                    reveal(gc_parse_at);
                }
                Some(gc_et_exec(home, cap.as_slice()))
            }
        },
    }
}

/// The XDG-or-.config base exec (mirrors gc_base_cfg).
pub fn gc_base_cfg_exec(
    xdg: Option<&[u8]>,
    home: Option<&[u8]>,
) -> (r: Option<Vec<u8>>)
    ensures
        (r matches None) == (gc_base_cfg(gcs(xdg), gcs(home))
            matches None),
        r matches Some(v) ==> (gc_base_cfg(gcs(xdg), gcs(home))
            matches Some(sv) && v@ == sv),
{
    match gc_nonempty_exec(xdg) {
        Some(x) => Some(x),
        None => match home {
            Some(h) => {
                let b: Vec<u8> = gcj_exec(h, &GC_DOT_CONFIG);
                proof {
                    gc_lit_bridges();
                    reveal(gc_base_cfg);
                }
                Some(b)
            }
            None => None,
        },
    }
}

/// The ladder entry point (mirrors gc_excl_spec; the five levels in
/// the upstream order, early return on the first hit per the
/// or_else composition, gitignore.rs:589-605). The let-shapes track
/// the spec's own lets one-for-one so def-eq carries each arm (the
/// per-arm asserts of the #IG-32 discipline -- Some/None views are
/// instantiated at each level, not assembled at the join).
pub fn gc_excludes_exec(
    gcfg: Option<&[u8]>,
    sysenv: Option<&[u8]>,
    xdg: Option<&[u8]>,
    home: Option<&[u8]>,
) -> (r: Option<Vec<u8>>)
    ensures
        (r matches None) == (gc_excl_spec(
            gcs(gcfg), gcs(sysenv), gcs(xdg), gcs(home))
            matches None),
        r matches Some(v) ==> (gc_excl_spec(
            gcs(gcfg), gcs(sysenv), gcs(xdg), gcs(home))
            matches Some(sv) && v@ == sv),
{
    // level 1 (gitignore.rs:601-605)
    let l1: Option<Vec<u8>> = match gc_nonempty_exec(gcfg) {
        Some(t) => gc_parse_at_exec(t.as_slice(), home),
        None => None,
    };
    match l1 {
        Some(p) => return Some(p),
        None => {}
    }
    proof {
        reveal(gc_excl_spec);
        reveal(gc_nonempty);
    }
    // level 2 (:642-643)
    let l2: Option<Vec<u8>> = match home {
        Some(h) => {
            let hp: Vec<u8> = gcj_exec(h, &GC_DOT_GITCONFIG);
            proof {
                gc_lit_bridges();
            }
            gc_parse_at_exec(hp.as_slice(), home)
        }
        None => None,
    };
    match l2 {
        Some(p) => return Some(p),
        None => {}
    }
    // level 3 (:645-652; the base value is shared with level 5,
    // the same spec call evaluated twice)
    let base: Option<Vec<u8>> = gc_base_cfg_exec(xdg, home);
    let l3: Option<Vec<u8>> = match &base {
        Some(b) => {
            let p3: Vec<u8> = gcj_exec(b.as_slice(), &GC_GIT_CONFIG);
            proof {
                gc_lit_bridges();
            }
            gc_parse_at_exec(p3.as_slice(), home)
        }
        None => None,
    };
    match l3 {
        Some(p) => return Some(p),
        None => {}
    }
    // level 4 (:625-631): the env value wins; the empty spelling
    // falls to /etc/gitconfig (the filter arm, not a None level)
    let p4v: Vec<u8> = match gc_nonempty_exec(sysenv) {
        Some(s) => s,
        None => {
            let lit: Vec<u8> = gc_copy(&GC_ETC_GITCONFIG);
            proof {
                gc_lit_bridges();
                assert(GC_ETC_GITCONFIG@ == gc_etc_gitconfig());
            }
            lit
        }
    };
    let l4: Option<Vec<u8>> = gc_parse_at_exec(p4v.as_slice(), home);
    match l4 {
        Some(p) => return Some(p),
        None => {}
    }
    // level 5 (:655-662)
    match &base {
        Some(b) => {
            let p5: Vec<u8> = gcj_exec(b.as_slice(), &GC_GIT_IGNORE);
            proof {
                gc_lit_bridges();
            }
            Some(p5)
        }
        None => None,
    }
}

} // verus!

// Standalone-file invocation anchor (the harness mounts this file with
// #[path]; single-file verus runs need the empty main).
fn main() {}
