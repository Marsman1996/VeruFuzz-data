//! semver 1.0.28 (pin `280ebcb6edac3aa4cdc545dbff8a26c5ac4861fe`) Verus
//! transcription tree root.
//!
//! Mirror and relaxation ledger (KVerus relax conventions; for details see
//! out/bug-finder-summary.md):
//! 1. `&str` is monomorphized to `&[u8]` throughout (vstd has no spec for
//!    `strip_prefix`/str slicing/`chars()`). The semver grammar surface is a
//!    pure ASCII byte domain, so
//!    the accept/reject decision surface is unchanged; in error messages
//!    the char of an out-of-domain input (multi-byte UTF-8) reduces to its
//!    first byte.
//! 2. The private carrier `Identifier` of the upstream
//!    `Prerelease`/`BuildMetadata` (code/src/identifier.rs, a fully unsafe
//!    pointer encoding with SSO + heap varints) is an unsafe block and is
//!    not transcribed; following its declared semantics ("a short-optimized
//!    string allowed to contain only the ASCII characters hyphen, dot,
//!    0-9, A-Z, a-z") it is modeled as `Vec<u8>`; `as_str()` is relaxed to
//!    `as_bytes()`. The `PartialEq`/`Ord` semantics are re-exported on the
//!    byte model by impls.rs (the upstream `ptr_eq` fast path of
//!    impls.rs:260-272 holds trivially under the equal-value model).
//! 3. The `char` slot of `ErrorKind` is relaxed to `u8` (this affects only
//!    the error-message fidelity of non-ASCII inputs; the decision surface
//!    is unchanged); `Error`'s `pub(crate) kind` is opened to `pub` for
//!    harness assertion observation (a pure visibility relaxation).
//! 4. `core::cmp::Ordering` is transcribed as the mirror enum `Ord2`
//!    (impls.rs; comparisons such as `ver.pre > cmp.pre` are expressed via
//!    `pre_cmp`/`Ord2`).
//! 5. The `version_req` recursion of parse.rs plus `unsafe { set_len }`
//!    plus `as_mut_ptr().add(depth).write` is a stack-write technique that
//!    is rewritten as a recursion assembling a Vec directly (equal assembly
//!    order, see the parse.rs ledger).
//! 6. The fmt Display / serde / std::error::Error / Hash / Deref layers are
//!    not transcribed (blocked), but the production semantics of `digits`
//!    (display.rs:156-162) are, in the parse.rs numeric model, the object of
//!    the doc-level `parse <-> display` roundtrip.
//!
//! Consumption: this file has no fn main; it is referenced by harness/ and
//! out/kverus-run/drv_lib.rs via `#[path = "../src/lib.rs"] mod semver;`
//! -- do not duplicate its specs.

use vstd::prelude::*;
use vstd::seq::Seq;

pub mod parse;
pub mod impls;
pub mod eval;

verus! {

/* ======================================================================
 * Public types (mirroring lib.rs:157-369 plus the parse.rs Error, error.rs Position)
 * ====================================================================== */

/// Origin: error.rs:19-26 `#[derive(Copy, Clone, Eq, PartialEq)] pub(crate) enum Position`
#[derive(PartialEq, Eq, Copy, Clone)]
pub enum Position {
    Major,
    Minor,
    Patch,
    Pre,
    Build,
}

/// Spec observation surface: Position -> its number (Major=0 .. Build=4), for ensures/harness assertions.
pub open spec fn pos_num(p: Position) -> int {
    match p {
        Position::Major => 0,
        Position::Minor => 1,
        Position::Patch => 2,
        Position::Pre => 3,
        Position::Build => 4,
    }
}

/// Origin: lib.rs:246-257 `pub enum Op` (#[non_exhaustive] is a lint-surface
/// attribute, not carried)
#[derive(PartialEq, Eq, Copy, Clone)]
pub enum Op {
    Exact,
    Greater,
    GreaterEq,
    Less,
    LessEq,
    Tilde,
    Caret,
    Wildcard,
}

/// Origin: lib.rs:203 `impl Op { const DEFAULT: Self = Self::Caret; }`
pub open spec const OP_DEFAULT: Op = Op::Caret;

/// Origin: error.rs:4-17 `pub(crate) enum ErrorKind`.
/// relax ledger 3: the `char` slot -> `u8`.
#[derive(PartialEq, Eq, Copy, Clone)]
pub enum ErrorKind {
    Empty,
    UnexpectedEnd(Position),
    UnexpectedChar(Position, u8),
    UnexpectedCharAfter(Position, u8),
    ExpectedCommaFound(Position, u8),
    LeadingZero(Position),
    Overflow(Position),
    EmptySegment(Position),
    IllegalCharacter(Position),
    WildcardNotTheOnlyComparator(u8),
    UnexpectedAfterWildcard,
    ExcessiveComparators,
}

/// Spec observation surface: the ErrorKind variant number (matching the error.rs declaration order).
pub open spec fn ek_num(k: ErrorKind) -> int {
    match k {
        ErrorKind::Empty => 0,
        ErrorKind::UnexpectedEnd(..) => 1,
        ErrorKind::UnexpectedChar(..) => 2,
        ErrorKind::UnexpectedCharAfter(..) => 3,
        ErrorKind::ExpectedCommaFound(..) => 4,
        ErrorKind::LeadingZero(..) => 5,
        ErrorKind::Overflow(..) => 6,
        ErrorKind::EmptySegment(..) => 7,
        ErrorKind::IllegalCharacter(..) => 8,
        ErrorKind::WildcardNotTheOnlyComparator(..) => 9,
        ErrorKind::UnexpectedAfterWildcard => 10,
        ErrorKind::ExcessiveComparators => 11,
    }
}

/// Spec observation surface: the Position carried by ErrorKind, as a number (-1 if none).
pub open spec fn ek_pos(k: ErrorKind) -> int {
    match k {
        ErrorKind::UnexpectedEnd(p) => pos_num(p),
        ErrorKind::UnexpectedChar(p, ..) => pos_num(p),
        ErrorKind::UnexpectedCharAfter(p, ..) => pos_num(p),
        ErrorKind::ExpectedCommaFound(p, ..) => pos_num(p),
        ErrorKind::LeadingZero(p) => pos_num(p),
        ErrorKind::Overflow(p) => pos_num(p),
        ErrorKind::EmptySegment(p) => pos_num(p),
        ErrorKind::IllegalCharacter(p) => pos_num(p),
        _ => -1,
    }
}

/// Spec observation surface: the byte value of the char slot carried by ErrorKind (256 if none).
pub open spec fn ek_char(k: ErrorKind) -> int {
    match k {
        ErrorKind::UnexpectedChar(.., c) => c as int,
        ErrorKind::UnexpectedCharAfter(.., c) => c as int,
        ErrorKind::ExpectedCommaFound(.., c) => c as int,
        _ => 256,
    }
}

/// Origin: parse.rs:21-23 `pub struct Error { pub(crate) kind: ErrorKind }`
/// relax ledger 3: kind opened to `pub` (harness assertion observation).
pub struct Error {
    pub kind: ErrorKind,
}

impl Error {
    /// Origin: parse.rs:146-150 `fn new(kind) -> Self`
    pub(crate) fn new(kind: ErrorKind) -> (r: Error)
        ensures
            r.kind == kind,
    {
        Error { kind }
    }
}

/* ======================================================================
 * Prerelease / BuildMetadata (the modeled carrier of lib.rs:308-369; relax ledger 2)
 * ====================================================================== */

/// Origin: lib.rs:308-311 `pub struct Prerelease { identifier: Identifier }`
/// relax ledger 2: Identifier(unsafe) -> `Vec<u8>`. Declaration semantics
/// per the upstream module header comment: "a short-optimized string
/// allowed to contain only the ASCII characters hyphen, dot, 0-9, A-Z, a-z".
pub struct Prerelease {
    pub bytes: Vec<u8>,
}

/// Origin: lib.rs:366-369 `pub struct BuildMetadata { identifier: Identifier }`
pub struct BuildMetadata {
    pub bytes: Vec<u8>,
}

impl Prerelease {
/// Origin: lib.rs:536-538 `pub const EMPTY: Self` -- a const body (spec mode
///     forbids an exec Vec::new) relaxed to an equivalent exec fn; the semantic surface is unchanged.
    pub fn EMPTY() -> (r: Self)
        ensures
            r.bytes@.len() == 0,
    {
        Prerelease { bytes: Vec::new() }
    }

    /// Origin: lib.rs:540-542 `pub fn new(text) -> Result<Self, Error>`
    ///     (via FromStr, parse.rs:122-132)
    pub fn new(text: &[u8]) -> (r: Result<Prerelease, Error>)
        ensures
            match r {
                Ok(p) => p.bytes@ == text@,
                Err(e) => true,
            },
    {
        self::parse::prerelease_from_str(text)
    }

    /// Origin: lib.rs:544-546 `pub fn as_str(&self)`; relax ledger 2: as_str -> as_bytes
    pub fn as_bytes(&self) -> (r: &[u8])
        ensures
            r@ == self.bytes@,
    {
        &self.bytes
    }

    /// Origin: lib.rs:548-550 `pub fn is_empty(&self)` (upstream goes through Identifier)
    pub fn is_empty(&self) -> (r: bool)
        ensures
            r == (self.bytes@.len() == 0),
    {
        self.bytes.len() == 0
    }
}

impl BuildMetadata {
    /// Origin: lib.rs:554-556 `pub const EMPTY: Self` -- the same relaxation as Prerelease::EMPTY.
    pub fn EMPTY() -> (r: Self)
        ensures
            r.bytes@.len() == 0,
    {
        BuildMetadata { bytes: Vec::new() }
    }

    /// Origin: lib.rs:558-560 `pub fn new(text)`
    pub fn new(text: &[u8]) -> (r: Result<BuildMetadata, Error>)
        ensures
            match r {
                Ok(b) => b.bytes@ == text@,
                Err(e) => true,
            },
    {
        self::parse::build_from_str(text)
    }

    /// Origin: lib.rs:562-564 `pub fn as_str(&self)`; relax ledger 2: as_str -> as_bytes
    pub fn as_bytes(&self) -> (r: &[u8])
        ensures
            r@ == self.bytes@,
    {
        &self.bytes
    }

    /// Origin: lib.rs:566-568 `pub fn is_empty(&self)`
    pub fn is_empty(&self) -> (r: bool)
        ensures
            r == (self.bytes@.len() == 0),
    {
        self.bytes.len() == 0
    }
}

/* ======================================================================
 * Version / VersionReq / Comparator (lib.rs:157-199)
 * ====================================================================== */

/// Origin: lib.rs:157-164 `pub struct Version`
pub struct Version {
    pub major: u64,
    pub minor: u64,
    pub patch: u64,
    pub pre: Prerelease,
    pub build: BuildMetadata,
}

/// Origin: lib.rs:183-186 `pub struct VersionReq`
pub struct VersionReq {
    pub comparators: Vec<Comparator>,
}

/// Origin: lib.rs:190-199 `pub struct Comparator`
pub struct Comparator {
    pub op: Op,
    pub major: u64,
    pub minor: Option<u64>,
    pub patch: Option<u64>,
    pub pre: Prerelease,
}

impl Version {
    /// Origin: lib.rs:389-397 `pub const fn new(major, minor, patch) -> Self`
    /// Upstream doc (lib.rs:372-388):
    ///   Create `Version` with an empty pre-release and build metadata.
    ///   Equivalent to:
    ///   # use semver::{BuildMetadata, Prerelease, Version};
    ///   #
    ///   # const fn new(major: u64, minor: u64, patch: u64) -> Version {
    ///   Version {
    ///   major,
    ///   minor,
    ///   patch,
    ///   pre: Prerelease::EMPTY,
    ///   build: BuildMetadata::EMPTY,
    ///   }
    ///   # }
    pub const fn new(major: u64, minor: u64, patch: u64) -> (r: Version)
        ensures
            r.major == major && r.minor == minor && r.patch == patch,
    {
        Version {
            major,
            minor,
            patch,
            pre: Prerelease { bytes: Vec::new() },
            build: BuildMetadata { bytes: Vec::new() },
        }
    }

    /// Origin: lib.rs:422-424 `pub fn parse(text: &str)`; relax ledger 1: &str -> &[u8]
    /// Upstream doc (lib.rs:399-421):
    ///   Create `Version` by parsing from string representation.
    ///   # Errors
    ///   Possible reasons for the parse to fail include:
    ///   - `1.0` &mdash; too few numeric components. A SemVer version must have
    ///   exactly three. If you are looking at something that has fewer than
    ///   three numbers in it, it's possible it is a `VersionReq` instead (with
    ///   an implicit default `^` comparison operator).
    ///   - `1.0.01` &mdash; a numeric component has a leading zero.
    ///   - `1.0.unknown` &mdash; unexpected character in one of the components.
    ///   - `1.0.0-` or `1.0.0+` &mdash; the pre-release or build metadata are
    ///   indicated present but empty.
    ///   - `1.0.0-alpha_123` &mdash; pre-release or build metadata have something
    ///   outside the allowed characters, which are `0-9`, `A-Z`, `a-z`, `-`,
    ///   and `.` (dot).
    ///   - `23456789999999999999.0.0` &mdash; overflow of a u64.
    pub fn parse(text: &[u8]) -> (r: Result<Version, Error>)
        ensures
            match r {
                Ok(v) => self::parse::ver_ok(text@, v),
                Err(e) => true,
            },
    {
        self::parse::version_from_str(text)
    }

    /// Origin: lib.rs:466-471 `pub fn cmp_precedence(&self, other: &Self) -> Ordering`
    /// relax ledger 4: Ordering -> Ord2 (defined in impls.rs). The semantics =
    /// upstream `Ord::cmp` on the `(major, minor, patch, &pre)` 4-tuple (the
    /// build component does not participate).
    /// Upstream doc (lib.rs:426-429):
    ///   Compare the major, minor, patch, and pre-release value of two versions,
    ///   disregarding build metadata. Versions that differ only in build metadata
    ///   are considered equal. This comparison is what the SemVer spec refers to
    ///   as "precedence".
    pub fn cmp_precedence(&self, other: &Self) -> (r: self::impls::Ord2)
        ensures
            r == self::parse::precedence_spec(
                self.major,
                self.minor,
                self.patch,
                self.pre.bytes@,
                other.major,
                other.minor,
                other.patch,
                other.pre.bytes@,
            ),
    {
        self::parse::cmp_precedence_model(
            self.major,
            self.minor,
            self.patch,
            &self.pre,
            other.major,
            other.minor,
            other.patch,
            &other.pre,
        )
    }
}

impl VersionReq {
    /// Origin: lib.rs:488-490 `pub const STAR: Self` -- the same EMPTY relaxation to an exec fn.
    /// Upstream doc (lib.rs:475-487):
    ///   A `VersionReq` with no constraint on the version numbers it matches.
    ///   Equivalent to `VersionReq::parse("*").unwrap()`.
    ///   In terms of comparators this is equivalent to `>=0.0.0`.
    ///   Counterintuitively a `*` VersionReq does not match every possible
    ///   version number. In particular, in order for *any* `VersionReq` to match
    ///   a pre-release version, the `VersionReq` must contain at least one
    ///   `Comparator` that has an explicit major, minor, and patch version
    ///   identical to the pre-release being matched, and that has a nonempty
    ///   pre-release component. Since `*` is not written with an explicit major,
    ///   minor, and patch version, and does not contain a nonempty pre-release
    ///   component, it does not match any pre-release versions.
    pub fn STAR() -> (r: Self)
        ensures
            r.comparators@.len() == 0,
    {
        VersionReq {
            comparators: Vec::new(),
        }
    }

    /// Origin: lib.rs:507-509 `pub fn parse(text: &str)`; relax ledger 1
    /// Upstream doc (lib.rs:492-506):
    ///   Create `VersionReq` by parsing from string representation.
    ///   # Errors
    ///   Possible reasons for the parse to fail include:
    ///   - `>a.b` &mdash; unexpected characters in the partial version.
    ///   - `@1.0.0` &mdash; unrecognized comparison operator.
    ///   - `^1.0.0, ` &mdash; unexpected end of input.
    ///   - `>=1.0 <2.0` &mdash; missing comma between comparators.
    ///   - `*.*` &mdash; unsupported wildcard syntax.
    pub fn parse(text: &[u8]) -> (r: Result<VersionReq, Error>)
        ensures
            match r {
                Ok(req) => self::parse::req_ok_spec(text@, req.comparators@),
                Err(e) => true,
            },
    {
        self::parse::version_req_from_str(text)
    }

    /// Origin: lib.rs:513-515 `pub fn matches(&self, version: &Version) -> bool`
    ///     (upstream delegates to eval::matches_req)
    /// Upstream doc (lib.rs:511-512):
    ///   Evaluate whether the given `Version` satisfies the version requirement
    ///   described by `self`.
    pub fn matches(&self, version: &Version) -> (r: bool)
        ensures
            r == self::eval::matches_req_spec(
                self.comparators@,
                version.major,
                version.minor,
                version.patch,
                version.pre.bytes@,
            ),
    {
        self::eval::matches_req(self, version)
    }
}

/// Origin: lib.rs:518-523 `impl Default for VersionReq` (= STAR) is not transcribed;
/// it is carried by the STAR constant and the req_ok_spec([]) ledger.

impl Comparator {
    /// Origin: lib.rs:526-528 `pub fn parse(text: &str)`; relax ledger 1
    pub fn parse(text: &[u8]) -> (r: Result<Comparator, Error>)
        ensures
            match r {
                Ok(c) => self::parse::comp_struct_ok(c),
                Err(e) => true,
            },
    {
        self::parse::comparator_from_str(text)
    }

    /// Origin: lib.rs:530-532 `pub fn matches(&self, version: &Version) -> bool`
    pub fn matches(&self, version: &Version) -> (r: bool)
        ensures
            r == self::eval::matches_comparator_spec(
                self.op,
                self.major,
                self.minor,
                self.patch,
                self.pre.bytes@,
                version.major,
                version.minor,
                version.patch,
                version.pre.bytes@,
            ),
    {
        self::eval::matches_comparator(self, version)
    }
}

/* ======================================================================
 * Shared byte-syntax spec model (used by parse/impls/eval/harness; the
 * verification fact source lives in this single place)
 * ====================================================================== */

pub open spec fn is_digit(b: u8) -> bool {
    0x30 <= b <= 0x39
}

/// Prefix decimal value ("123" -> 123): the meaning of len <= len(input) is guaranteed by the caller.
pub open spec fn num_str_value(input: Seq<u8>, len: int) -> int
    recommends
        0 <= len,
    decreases
        len,
{
    if len <= 0 {
        0
    } else {
        num_str_value(input, len - 1) * 10 + (input[len - 1] - 0x30)
    }
}

/// Index of the first '.', or -1 if none.
pub open spec fn first_dot(s: Seq<u8>) -> int {
    first_dot_from(s, 0)
}

/// The from-variant of first_dot (the interface consumed by the scanning lemmas).
pub open spec fn first_dot_from(s: Seq<u8>, from: int) -> int
    recommends
        0 <= from,
    decreases
        s.len() - from,
{
    if from >= s.len() {
        -1
    } else if s[from] == 0x2e {
        from
    } else {
        first_dot_from(s, from + 1)
    }
}

/// Mid-state predicate on the '.'-separated segment structure: all segments
/// non-empty AND a trailing '.' allowed (the identifier scan is momentarily
/// in this state right after a segment advance). Non-recursive pairwise form:
/// every '.' has i>0 with a non-'.' predecessor, and no leading '.' is left.
pub open spec fn no_empty_segment(s: Seq<u8>) -> bool {
    forall|i: int|
        #![trigger s[i]]
        (0 <= i < s.len()) ==> (s[i] != 0x2e || (0 < i && s[i - 1] != 0x2e))
}

} // verus!
