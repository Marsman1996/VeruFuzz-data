//! ignore 0.4.34 (pin `178cc027`) -- Verus transcription tree, crate root
//! (mirrors upstream `crates/ignore/src/lib.rs`), batch IG1.
//!
//! Upstream: github.com/BurntSushi/ripgrep @
//! 178cc027e283fd965cb72d0a7395b219eada170c (crates/ignore = 0.4.34).
//! This first batch carries the lib.rs core surface: the `Error` enum
//! (lib.rs:66-120) with its predicate family (is_partial / is_io /
//! io_error / into_io_error / depth, lib.rs:156-260), the private tagger
//! helpers (with_path / with_depth / tagged, lib.rs:262-284), the
//! `Match<T>` result enum with its combinators (lib.rs:409-487), and
//! `PartialErrorBuilder` (lib.rs:372-407). The `pathutil` module mount is
//! the IG1 companion (`mod pathutil;`, upstream lib.rs:62). Module
//! visibility is opened pub for the harness `#[path]` mounts (single
//! source of verified facts; nothing re-copied).
//!
//! Upstream pieces NOT in this batch (deferred with anchors):
//! - `impl Clone for Error` (lib.rs:122-154): the `Error::Io` clone leg
//!   reconstructs an io::Error via `raw_os_error` / `kind + to_string`
//!   (lib.rs:139-144) -- trusted io face, deferred.
//! - `impl std::error::Error for Error` (lib.rs:310-325) and
//!   `impl std::fmt::Display` (lib.rs:327-364): the string tier is
//!   outside the verus surface (formatting faces).
//! - `impl From<std::io::Error> for Error` (lib.rs:366-370): the io face
//!   constructor leg, deferred with the Clone leg.
//! - `Error::from_walkdir` (lib.rs:287-307): consumes `walkdir::Error`
//!   -- the walkdir trusted face mounts with IG7.
//! - the `#[cfg(test)]` module (lib.rs:489-549): a temp-dir fs helper,
//!   runtime-only infra per inventory section 9.
//! - the `pub use` re-export block (lib.rs:51-55): trimmed IG8 form
//!   below (the parallel-face symbols ride the IG7 recorded cut).
//!
//! Modeling declarations:
//! - **PathBuf face:** `Error::WithPath { path: PathBuf }` and
//!   `Error::Loop { ancestor, child }` carry `PathBuf` payloads upstream;
//!   the twin models them as byte carriers (`PathBytes`, view over
//!   `Seq<u8>`), the same byte-path convention as pathutil (kept uniform
//!   crate-wide for the IG2/IG3 gitignore twins).
//! - **io::Error face:** `Error::Io(std::io::Error)` is modeled by the
//!   opaque data face `IoErrorFace` below. The only behavioral content
//!   the Error predicates consume is *variant identity* (is it an Io?)
//!   -- the raw_os_error / kind / display internals are trusted-face
//!   legs (with the Clone/From legs above).
//! - **String face:** the `String` payloads of `Glob`, `UnrecognizedFileType`
//!   and `Glob.err` are byte carriers (`Vec<u8>`); no string semantics is
//!   consumed by this batch's obligations.

use vstd::prelude::*;
use vstd::seq::Seq;

pub mod gitignore;
pub mod pathutil;
// The IG4 module mounts (upstream lib.rs:57-62: `mod default_types;`
// `pub mod overrides;` `pub mod types;` -- the first opened pub for
// the harness #[path] mounts per the crate-wide convention, the other
// two already pub upstream).
pub mod default_types;
pub mod overrides;
pub mod types;
// The IG5 module mount (upstream lib.rs:59 `mod dir;`) -- opened pub
// for the harness `#[path]` mounts, the crate-wide convention here.
pub mod dir;
// The IG6 module mount (upstream lib.rs:61 `mod incremental;`) -- opened
// pub for the harness `#[path]` mounts, the crate-wide convention here.
// (PARKED at IG6 batch close while the walk-chain proofs were in the
// #IG-19 grind; re-mounted at the IG7 batch open once the chain went
// green -- the ledger sits in out/kverus-run/IG6/notes.md deferred 1.)
pub mod incremental;
// The IG7 module mount (upstream lib.rs:63 `pub mod walk;`) --
// opened pub for the harness `#[path]` mounts, the crate-wide
// convention here. (The functional core is real: the DirEntry
// dispatch family, the from_walkdir mapping, the skip tier laws,
// the builder clamps and the WalkEventIter state machine; the
// walkdir/fs faces, the assembly legs and the crossbeam parallel
// face are the trusted-contract tier of this batch -- the ledger
// in src/walk.rs's header and out/kverus-run/IG7/notes.md.)
pub mod walk;

// The IG8 API-surface completion (upstream lib.rs:51-55's `pub use`
// re-export block): the parallel-face symbols (Walk, WalkParallel,
// WalkState, ParallelVisitor, ParallelVisitorBuilder) ride the
// IG7 recorded cut -- the twin keeps no items of those names -- so
// this trimmed re-export carries exactly the existing faces (the
// `self::` spelling per the #IG-7 mount rule: `crate::` breaks
// under the harness #[path] mounts).
pub use self::incremental::{IncrementalIgnore, IncrementalMatch};
pub use self::walk::{DirEntry, WalkBuilder};

verus! {

// =========================================================================
// Faces: PathBytes (PathBuf) and IoErrorFace (std::io::Error)
// =========================================================================

/// The byte-path carrier (`PathBuf` face; see the header note).
pub struct PathBytes {
    /// The path bytes (upstream: the `PathBuf` value).
    pub bytes: Vec<u8>,
}

/// The view of a PathBytes payload.
pub open spec fn path_bytes_view(p: &PathBytes) -> Seq<u8> {
    p.bytes@
}

/// The trusted data face for `std::io::Error` (see the header note): a
/// value distinguishable from every other payload; nothing about the io
/// internals enters the twin.
pub struct IoErrorFace {
    /// An abstract payload (the io::Error internals stay outside).
    pub repr: u64,
}

impl IoErrorFace {
    /// Construct an abstract io face value (the upstream constructors are
    /// the fs / `From` legs; the harness needs witness Io variants).
    pub fn new(repr: u64) -> (r: IoErrorFace)
        ensures r.repr == repr,
    {
        IoErrorFace { repr }
    }
}

// =========================================================================
// Error -- upstream lib.rs:66-120
// =========================================================================
//
// Upstream doc (lib.rs:66, verbatim):
//   "Represents an error that can occur when parsing a gitignore file."

/// Origin enum (lib.rs:67-120); every variant doc quoted verbatim.
/// (the `err` field appears as Box<Error> in three variants and Vec<u8>
/// payload names differ elsewhere; `->err` sugar is not used by the twin
/// -- the inconsistency is the upstream layout, kept as is.)
#[allow(inconsistent_fields)]
pub enum Error {
    /// A collection of "soft" errors. These occur when adding an ignore
    /// file partially succeeded.
    Partial(Vec<Error>),
    /// An error associated with a specific line number.
    WithLineNumber {
        /// The line number.
        line: u64,
        /// The underlying error.
        err: Box<Error>,
    },
    /// An error associated with a particular file path.
    WithPath {
        /// The file path.
        path: PathBytes,
        /// The underlying error.
        err: Box<Error>,
    },
    /// An error associated with a particular directory depth when
    /// recursively walking a directory.
    WithDepth {
        /// The directory depth.
        depth: usize,
        /// The underlying error.
        err: Box<Error>,
    },
    /// An error that occurs when a file loop is detected when traversing
    /// symbolic links.
    Loop {
        /// The ancestor file path in the loop.
        ancestor: PathBytes,
        /// The child file path in the loop.
        child: PathBytes,
    },
    /// An error that occurs when doing I/O, such as reading an ignore
    /// file.
    Io(IoErrorFace),
    /// An error that occurs when trying to parse a glob.
    Glob {
        /// The original glob that caused this error. This glob, when
        /// available, always corresponds to the glob provided by an end
        /// user. e.g., It is the glob as written in a `.gitignore` file.
        ///
        /// (This glob may be distinct from the glob that is actually
        /// compiled, after accounting for `gitignore` semantics.)
        glob: Option<Vec<u8>>,
        /// The underlying glob error as a string.
        err: Vec<u8>,
    },
    /// A type selection for a file type that is not defined.
    UnrecognizedFileType(Vec<u8>),
    /// A user specified file type definition could not be parsed.
    InvalidDefinition,
}

// =========================================================================
// Error predicates -- upstream lib.rs:156-260
// =========================================================================
//
// Upstream doc (lib.rs:157-160, verbatim):
//   "Returns true if this is a partial error.
//    A partial error occurs when only some operations failed while others
//    may have succeeded. For example, an ignore file may contain an
//    invalid glob among otherwise valid globs."

/// Spec track of `Error::is_partial` (lib.rs:162-170): Partial itself, or
/// any tagged wrapper holding a partial error.
pub open spec fn is_partial_spec(e: &Error) -> bool
    decreases e
{
    match e {
        Error::Partial(_) => true,
        Error::WithLineNumber { err, .. } => is_partial_spec(err),
        Error::WithPath { err, .. } => is_partial_spec(err),
        Error::WithDepth { err, .. } => is_partial_spec(err),
        Error::Loop { .. } => false,
        Error::Io(_) => false,
        Error::Glob { .. } => false,
        Error::UnrecognizedFileType(_) => false,
        Error::InvalidDefinition => false,
    }
}

/// Origin Rust (lib.rs:162-170), transcribed verbatim (Box derefs and
/// Vec indexing materialized per the modeling declarations).
pub fn is_partial(e: &Error) -> (r: bool)
    ensures r == is_partial_spec(e)
    decreases e
{
    match e {
        Error::Partial(_) => true,
        Error::WithLineNumber { err, .. } => is_partial(err),
        Error::WithPath { err, .. } => is_partial(err),
        Error::WithDepth { err, .. } => is_partial(err),
        Error::Loop { .. } => false,
        Error::Io(_) => false,
        Error::Glob { .. } => false,
        Error::UnrecognizedFileType(_) => false,
        Error::InvalidDefinition => false,
    }
}

//
// Upstream doc (lib.rs:172, verbatim):
//   "Returns true if this error is exclusively an I/O error."
//
// NB: the word "exclusively" is what makes `Partial([io])` count and
// `Partial([io, io])` not (lib.rs:175:
// `errs.len() == 1 && errs[0].is_io()`); a `WithLineNumber { Io(_) }`
// still counts (it descends, lib.rs:176).

/// Spec track of `Error::is_io` (lib.rs:173-185).
pub open spec fn is_io_spec(e: &Error) -> bool
    decreases e
{
    match e {
        Error::Partial(errs) => errs@.len() == 1 && is_io_spec(&errs[0]),
        Error::WithLineNumber { err, .. } => is_io_spec(err),
        Error::WithPath { err, .. } => is_io_spec(err),
        Error::WithDepth { err, .. } => is_io_spec(err),
        Error::Loop { .. } => false,
        Error::Io(_) => true,
        Error::Glob { .. } => false,
        Error::UnrecognizedFileType(_) => false,
        Error::InvalidDefinition => false,
    }
}

/// Origin Rust (lib.rs:173-185), transcribed verbatim.
pub fn is_io(e: &Error) -> (r: bool)
    ensures r == is_io_spec(e)
    decreases e
{
    match e {
        Error::Partial(errs) => {
            if errs.len() == 1 {
                let i = 0;
                is_io(&errs[i])
            } else {
                false
            }
        }
        Error::WithLineNumber { err, .. } => is_io(err),
        Error::WithPath { err, .. } => is_io(err),
        Error::WithDepth { err, .. } => is_io(err),
        Error::Loop { .. } => false,
        Error::Io(_) => true,
        Error::Glob { .. } => false,
        Error::UnrecognizedFileType(_) => false,
        Error::InvalidDefinition => false,
    }
}

//
// Upstream doc (lib.rs:187-195, verbatim):
//   "Inspect the original [`std::io::Error`] if there is one.
//    [`None`] is returned if the [`Error`] doesn't correspond to an
//    [`std::io::Error`]. This might happen, for example, when the error
//    was produced because a cycle was found in the directory tree while
//    following symbolic links.
//    This method returns a borrowed value that is bound to the lifetime
//    of the [`Error`]. To obtain an owned value, the [`into_io_error`]
//    can be used instead."

/// Spec track of `Error::io_error` (lib.rs:207-225).
pub open spec fn io_error_spec<'a>(e: &'a Error) -> Option<&'a IoErrorFace>
    decreases e
{
    match e {
        Error::Partial(errs) => {
            if errs@.len() == 1 { io_error_spec(&errs[0]) } else { None }
        }
        Error::WithLineNumber { err, .. } => io_error_spec(err),
        Error::WithPath { err, .. } => io_error_spec(err),
        Error::WithDepth { err, .. } => io_error_spec(err),
        Error::Loop { .. } => None,
        Error::Io(e2) => Some(e2),
        Error::Glob { .. } => None,
        Error::UnrecognizedFileType(_) => None,
        Error::InvalidDefinition => None,
    }
}

/// Origin Rust (lib.rs:207-225): the borrowed io inspection.
pub fn io_error(e: &Error) -> (r: Option<&IoErrorFace>)
    ensures r == io_error_spec(e)
    decreases e
{
    match e {
        Error::Partial(errs) => {
            if errs.len() == 1 {
                let i = 0;
                io_error(&errs[i])
            } else {
                None
            }
        }
        Error::WithLineNumber { err, .. } => io_error(err),
        Error::WithPath { err, .. } => io_error(err),
        Error::WithDepth { err, .. } => io_error(err),
        Error::Loop { .. } => None,
        Error::Io(e2) => Some(e2),
        Error::Glob { .. } => None,
        Error::UnrecognizedFileType(_) => None,
        Error::InvalidDefinition => None,
    }
}

//
// Upstream doc (lib.rs:227-229, verbatim):
//   "Similar to [`io_error`] except consumes self to convert to the
//    original [`std::io::Error`] if one exists."

/// Spec track of `Error::into_io_error` (lib.rs:232-250).
pub open spec fn into_io_error_spec(e: Error) -> Option<IoErrorFace>
    decreases e
{
    match e {
        Error::Partial(errs) => {
            if errs@.len() == 1 { into_io_error_spec(errs[0]) } else { None }
        }
        Error::WithLineNumber { err, .. } => into_io_error_spec(*err),
        Error::WithPath { err, .. } => into_io_error_spec(*err),
        Error::WithDepth { err, .. } => into_io_error_spec(*err),
        Error::Loop { .. } => None,
        Error::Io(e2) => Some(e2),
        Error::Glob { .. } => None,
        Error::UnrecognizedFileType(_) => None,
        Error::InvalidDefinition => None,
    }
}

/// Origin Rust (lib.rs:232-250): the consuming variant (`errs.remove(0)`,
/// lib.rs:236, is the length-one head read).
pub fn into_io_error(e: Error) -> (r: Option<IoErrorFace>)
    ensures r == into_io_error_spec(e)
    decreases e
{
    match e {
        Error::Partial(mut errs) => {
            if errs.len() == 1 {
                // errs.remove(0).into_io_error()
                let head = errs.remove(0);
                into_io_error(head)
            } else {
                None
            }
        }
        Error::WithLineNumber { err, .. } => into_io_error(*err),
        Error::WithPath { err, .. } => into_io_error(*err),
        Error::WithDepth { err, .. } => into_io_error(*err),
        Error::Loop { .. } => None,
        Error::Io(e2) => Some(e2),
        Error::Glob { .. } => None,
        Error::UnrecognizedFileType(_) => None,
        Error::InvalidDefinition => None,
    }
}

//
// Upstream doc (lib.rs:253-254, verbatim):
//   "Returns a depth associated with recursively walking a directory (if
//    this error was generated from a recursive directory iterator)."

/// Spec track of `Error::depth` (lib.rs:254-260).
pub open spec fn depth_spec(e: &Error) -> Option<usize>
    decreases e
{
    match e {
        Error::WithPath { err, .. } => depth_spec(err),
        Error::WithDepth { depth, .. } => Some(*depth),
        Error::Partial(_) => None,
        Error::WithLineNumber { .. } => None,
        Error::Loop { .. } => None,
        Error::Io(_) => None,
        Error::Glob { .. } => None,
        Error::UnrecognizedFileType(_) => None,
        Error::InvalidDefinition => None,
    }
}

/// Origin Rust (lib.rs:254-260), transcribed verbatim.
pub fn depth(e: &Error) -> (r: Option<usize>)
    ensures r == depth_spec(e)
    decreases e
{
    match e {
        Error::WithPath { err, .. } => depth(err),
        Error::WithDepth { depth, .. } => Some(*depth),
        _ => None,
    }
}

// =========================================================================
// Private tagger helpers -- upstream lib.rs:262-284
// =========================================================================
//
// Upstream doc (lib.rs:262, verbatim):
//   "Turn an error into a tagged error with the given file path."
// Upstream doc (lib.rs:271, verbatim):
//   "Turn an error into a tagged error with the given depth."
// Upstream doc (lib.rs:275-276, verbatim):
//   "Turn an error into a tagged error with the given file path and line
//    number. If path is empty, then it is omitted from the error."

/// Spec view of the WithPath payload (the tagger contracts).
pub open spec fn with_path_payload(e: &Error) -> Seq<u8>
{
    match e {
        Error::WithPath { path, .. } => path_bytes_view(path),
        _ => Seq::empty(),
    }
}

/// Spec view of the WithLineNumber payload.
pub open spec fn with_line_payload(e: &Error) -> Option<u64>
{
    match e {
        Error::WithLineNumber { line, .. } => Some(*line),
        _ => None,
    }
}

/// Spec view of the WithPath inner error (Box deref).
pub open spec fn with_path_inner<'a>(e: &'a Error) -> &'a Error
{
    match e {
        Error::WithPath { err, .. } => &**err,
        _ => e,
    }
}

/// Spec track of the line payload under any number of tagger wrappers
/// (the `error_tagged` shape is WithPath { WithLineNumber { .. } }; the
/// top-level-only `with_line_payload` does not see through the WithPath
/// layer, so the add()-loop error-view fold (IG3's io-typing rematch)
/// uses this recursive view instead).
pub open spec fn line_nested(e: &Error) -> Option<u64>
    decreases e
{
    match e {
        Error::WithLineNumber { line, .. } => Some(*line),
        Error::WithPath { err, .. } => line_nested(&**err),
        Error::WithDepth { err, .. } => line_nested(&**err),
        _ => None,
    }
}

/// Spec track of the Glob payload under any number of tagger wrappers
/// (same rationale as `line_nested`; the add()-loop fold reads the
/// original-glob payload through the tagger chain).
pub open spec fn glob_nested(e: &Error) -> Option<Seq<u8>>
    decreases e
{
    match e {
        Error::Glob { glob, .. } => match glob {
            Some(v) => Some(v@),
            None => None,
        },
        Error::WithLineNumber { err, .. } => glob_nested(&**err),
        Error::WithPath { err, .. } => glob_nested(&**err),
        Error::WithDepth { err, .. } => glob_nested(&**err),
        _ => None,
    }
}

/// `Error::with_path` (lib.rs:263-268): `path.as_ref().to_path_buf()`
/// materializes as `slice_to_vec` over the byte face.
pub fn error_with_path(e: Error, path: &[u8]) -> (r: Error)
    ensures
        r matches Error::WithPath { .. }
            && with_path_payload(&r) == path@
            && *with_path_inner(&r) == e,
{
    Error::WithPath {
        path: PathBytes { bytes: vstd::slice::slice_to_vec(path) },
        err: Box::new(e),
    }
}

/// `Error::with_depth` (lib.rs:271-273).
pub fn error_with_depth(e: Error, depth: usize) -> (r: Error)
    ensures
        r matches Error::WithDepth { .. }
            && with_depth_value(&r) == depth,
{
    Error::WithDepth { depth, err: Box::new(e) }
}

/// Spec view of the WithDepth payload.
pub open spec fn with_depth_value(e: &Error) -> usize {
    match e {
        Error::WithDepth { depth, .. } => *depth,
        _ => 0,
    }
}

/// `Error::tagged` (lib.rs:277-284): the line tagger, with the
/// empty-path omission (lib.rs:280-283,
/// `if path.as_ref().as_os_str().is_empty() { return errline; }`).
pub fn error_tagged(e: Error, path: &[u8], lineno: u64) -> (r: Error)
    ensures
        path.len() == 0 ==>
            (r matches Error::WithLineNumber { .. }
                && with_line_payload(&r) == Some(lineno)),
        path.len() > 0 ==>
            (r matches Error::WithPath { .. }
                && with_path_payload(&r) == path@
                && ({ let inner: &Error = with_path_inner(&r);
                      inner matches Error::WithLineNumber { .. } })),
        // IG3 strengthening (the io-typing rematch of the IG2-deferred
        // element-level error claims): whatever the wrapper shape, the
        // line number rides one layer down and the wrapped error's kind
        // survives the tagger chain (is_io / glob payloads).
        line_nested(&r) == Some(lineno),
        is_io_spec(&r) == is_io_spec(&e),
        glob_nested(&r) == glob_nested(&e),
{
    // let errline = Error::WithLineNumber { line: lineno, err: Box::new(self) };
    let errline = Error::WithLineNumber { line: lineno, err: Box::new(e) };
    if path.len() == 0 {
        proof {
            reveal_with_fuel(line_nested, 2);
            reveal_with_fuel(is_io_spec, 2);
            reveal_with_fuel(glob_nested, 2);
        }
        return errline;
    }
    // errline.with_path(path)
    let wrapped = Error::WithPath {
        path: PathBytes { bytes: vstd::slice::slice_to_vec(path) },
        err: Box::new(errline),
    };
    proof {
        // the wrapper chain: WithPath { WithLineNumber { err } } -- the
        // recursive views read through one Box deref on each level
        reveal_with_fuel(line_nested, 3);
        reveal_with_fuel(is_io_spec, 3);
        reveal_with_fuel(glob_nested, 3);
        assert(line_nested(&wrapped) == line_nested(with_path_inner(&wrapped)));
        assert(is_io_spec(&wrapped) == is_io_spec(with_path_inner(&wrapped)));
        assert(glob_nested(&wrapped) == glob_nested(with_path_inner(&wrapped)));
        let inner = with_path_inner(&wrapped);
        assert(*inner == errline);
        assert(line_nested(inner) == line_nested(&errline));
    }
    wrapped
}

// =========================================================================
// PartialErrorBuilder -- upstream lib.rs:372-407
// =========================================================================
//
// No upstream doc on this private struct; its folding rules are the IG1
// obligation face (the DP14 single-vs-list wrappers, lib.rs:398-406).
// Origin Rust (lib.rs:372-407) transcribed fn-for-fn.

/// `PartialErrorBuilder` (lib.rs:372-373): a Vec-stack accumulator
/// (`#[derive(Debug, Default)]` upstream; the Default view is the empty
/// stack).
pub struct PartialErrorBuilder {
    /// The stacked errors (upstream: the private `Vec<Error>`; opened pub
    /// for the spec views -- the mount-visibility convention).
    pub errs: Vec<Error>,
}

/// The stack view (spec, borrowed form for &mut method posts).
pub open spec fn peb_stack(s: &PartialErrorBuilder) -> Seq<Error> {
    s.errs@
}

/// The stack view (spec, by-value form for the consuming fn's post).
pub open spec fn peb_stack_val(s: PartialErrorBuilder) -> Seq<Error> {
    s.errs@
}

impl PartialErrorBuilder {
    /// `PartialErrorBuilder::default` (lib.rs:372).
    pub fn new() -> (r: PartialErrorBuilder)
        ensures
            peb_stack(&r) == Seq::empty(),
            r.errs@ == Seq::empty(),
    {
        PartialErrorBuilder { errs: Vec::new() }
    }

    /// `push` (lib.rs:376-378): unconditionally append.
    pub fn push(&mut self, err: Error)
        ensures final(self).errs@ == old(self).errs@.push(err),
    {
        self.errs.push(err);
    }

    /// `push_ignore_io` (lib.rs:380-384): drop io errors, keep the rest;
    /// this is the `Gitignore::new`-side discipline "I/O errors are
    /// ignored" (DP2's machinery leg, upstream doc gitignore.rs:97-102).
    pub fn push_ignore_io(&mut self, err: Error)
        ensures
            is_io_spec(&err) ==> final(self).errs@ == old(self).errs@,
            !is_io_spec(&err) ==> final(self).errs@ == old(self).errs@.push(err),
    {
        if !is_io(&err) {
            self.push(err);
        }
    }

    /// `maybe_push` (lib.rs:386-390).
    pub fn maybe_push(&mut self, err: Option<Error>)
        ensures
            err matches Some(e) ==> final(self).errs@ == old(self).errs@.push(e),
            err matches None ==> final(self).errs@ == old(self).errs@,
    {
        if let Some(err) = err {
            self.push(err);
        }
    }

    /// `maybe_push_ignore_io` (lib.rs:392-396).
    pub fn maybe_push_ignore_io(&mut self, err: Option<Error>)
        ensures
            err matches Some(e) ==> ((
                    is_io_spec(&e) ==> final(self).errs@ == old(self).errs@)
                && (!is_io_spec(&e) ==> final(self).errs@ == old(self).errs@.push(e))),
            err matches None ==> final(self).errs@ == old(self).errs@,
    {
        if let Some(err) = err {
            self.push_ignore_io(err);
        }
    }

    /// `into_error_option` (lib.rs:398-405): empty -> None, single ->
    /// Some(that error, unwrapped), plural -> Some(Partial(the list)).
    /// NB the single case returns whatever the one stacked error is,
    /// verbatim -- if the stack is `[Partial([..])]` of length one the
    /// result is `Some(Partial(..))` (no re-wrap happens; the plural wrap
    /// is only for length >= 2).
    pub fn into_error_option(self) -> (r: Option<Error>)
        ensures
            peb_stack_val(self) == Seq::empty() ==> r matches None,
            peb_stack_val(self).len() == 1 ==>
                (r matches Some(e) && peb_stack_val(self)[0] == e),
            peb_stack_val(self).len() >= 2 ==>
                (r matches Some(e2) && e2 matches Error::Partial(_)
                    // IG3 strengthening (the errs-content rematch): the
                    // plural wrap carries the stack itself
                    && (match &e2 {
                        Error::Partial(errs) => errs@ == peb_stack_val(self),
                        _ => false,
                    })),
    {
        let mut errs = self.errs;
        // if self.0.is_empty() { None }
        if errs.len() == 0 {
            None
        } else if errs.len() == 1 {
            // Some(self.0.pop().unwrap())
            let head = errs.pop();
            match head {
                Some(err) => Some(err),
                None => None,
            }
        } else {
            // Some(Error::Partial(self.0))
            Some(Error::Partial(errs))
        }
    }
}

// =========================================================================
// Match<T> -- upstream lib.rs:409-487
// =========================================================================
//
// Upstream doc (lib.rs:410-414, verbatim):
//   "The result of a glob match.
//    The type parameter `T` typically refers to a type that provides more
//    information about a particular match. For example, it might identify
//    the specific gitignore file and the specific glob pattern that caused
//    the match."

/// Origin enum (lib.rs:415-425), variant docs verbatim.
pub enum Match<T> {
    /// The path didn't match any glob.
    None,
    /// The highest precedent glob matched indicates the path should be
    /// ignored.
    Ignore(T),
    /// The highest precedent glob matched indicates the path should be
    /// whitelisted.
    Whitelist(T),
}

impl<T> Match<T> {
    /// Upstream doc (lib.rs:428, verbatim):
    ///   "Returns true if the match result didn't match any globs."
    pub fn is_none(&self) -> (r: bool)
        ensures r == (self matches Match::None)
    {
        self matches Match::None
    }

    /// Upstream doc (lib.rs:436, verbatim):
    ///   "Returns true if the match result implies the path should be
    ///    ignored."
    pub fn is_ignore(&self) -> (r: bool)
        ensures r == (self matches Match::Ignore(_))
    {
        self matches Match::Ignore(_)
    }

    /// Upstream doc (lib.rs:443-444, verbatim):
    ///   "Returns true if the match result implies the path should be
    ///    whitelisted."
    pub fn is_whitelist(&self) -> (r: bool)
        ensures r == (self matches Match::Whitelist(_))
    {
        self matches Match::Whitelist(_)
    }

    /// Upstream doc (lib.rs:453-454, verbatim):
    ///   "Inverts the match so that `Ignore` becomes `Whitelist` and
    ///    `Whitelist` becomes `Ignore`. A non-match remains the same."
    pub fn invert(self) -> (r: Match<T>)
        ensures
            r matches Match::None == self matches Match::None,
            (r matches Match::Ignore(_)) == (self matches Match::Whitelist(_)),
            (r matches Match::Whitelist(_)) == (self matches Match::Ignore(_)),
    {
        match self {
            Match::None => Match::None,
            Match::Ignore(t) => Match::Whitelist(t),
            Match::Whitelist(t) => Match::Ignore(t),
        }
    }

    /// Upstream doc (lib.rs:463, verbatim):
    ///   "Return the value inside this match if it exists."
    pub fn inner(&self) -> (r: Option<&T>)
        ensures r == inner_spec(self)
    {
        match self {
            Match::None => None,
            Match::Ignore(t) => Some(t),
            Match::Whitelist(t) => Some(t),
        }
    }

    /// Upstream doc (lib.rs:473-474, verbatim):
    ///   "Apply the given function to the value inside this match.
    ///    If the match has no value, then return the match unchanged."
    ///
    /// Modeling note: the generic `FnOnce(T) -> U` payload of upstream
    /// lib.rs:475-481 is carried verbatim at the exec face, with the
    /// closure's action anchored by `call_requires` (the caller contract
    /// face; the exact value law lives in the spec twin `map_spec`).
    pub fn map<U, F: Fn(T) -> U>(self, f: F) -> (r: Match<U>)
        requires forall|t: T| call_requires(f, (t,)),
        ensures
            (r matches Match::None) == (self matches Match::None),
            (r matches Match::Ignore(_)) == (self matches Match::Ignore(_)),
            (r matches Match::Whitelist(_)) == (self matches Match::Whitelist(_)),
    {
        match self {
            Match::None => Match::None,
            Match::Ignore(t) => Match::Ignore(f(t)),
            Match::Whitelist(t) => Match::Whitelist(f(t)),
        }
    }

    /// Upstream doc (lib.rs:483, verbatim):
    ///   "Return the match if it is not none. Otherwise, return other."
    pub fn or(self, other: Self) -> (r: Self)
        ensures
            self matches Match::None ==> r == other,
            !(self matches Match::None) ==> r == self,
    {
        // if self.is_none() { other } else { self }
        if self.is_none() {
            other
        } else {
            self
        }
    }
}

/// Spec track of `Match::inner` (the payload reference of a non-None
/// match; the None arm is None).
pub open spec fn inner_spec<T>(m: &Match<T>) -> Option<&T> {
    match m {
        Match::None => None,
        Match::Ignore(t) => Some(t),
        Match::Whitelist(t) => Some(t),
    }
}

/// Spec track of `Match::map` (the exact value law; the payload is a
/// spec_fn so the law is first-class in specs).
pub open spec fn map_spec<T, U>(m: Match<T>, f: spec_fn(T) -> U) -> Match<U> {
    match m {
        Match::None => Match::None,
        Match::Ignore(t) => Match::Ignore(f(t)),
        Match::Whitelist(t) => Match::Whitelist(f(t)),
    }
}

/// Spec track of `Match::invert` (the value-preservation view).
pub open spec fn invert_of_match<T>(m: Match<T>) -> Match<T> {
    match m {
        Match::None => Match::None,
        Match::Ignore(t) => Match::Whitelist(t),
        Match::Whitelist(t) => Match::Ignore(t),
    }
}

}

// Standalone-file invocation anchor (the harness mounts this file with
// #[path]; single-file verus runs need the empty main).
fn main() {}
