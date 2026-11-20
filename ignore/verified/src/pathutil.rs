//! ignore 0.4.34 (pin `178cc027`) -- Verus transcription of upstream
//! `crates/ignore/src/pathutil.rs` (218 upstream lines), batch IG1.
//!
//! Upstream: github.com/BurntSushi/ripgrep @
//! 178cc027e283fd965cb72d0a7395b219eada170c (crates/ignore = 0.4.34).
//! This file is the **src zone** twin (the two-zone split of the glob
//! precedent): spec models + verbatim exec transcriptions + platform-oracle
//! and DP33 material-chain theorems live here; the UT assertion theorems
//! live in verified/harness/ut_ig1.rs.
//!
//! Modeling declarations (deviations declared, upstream line anchors cited):
//! - **Path bytes:** the upstream unix arms all operate on
//!   `path.as_os_str().as_bytes()` / `as_encoded_bytes()`; the twin models
//!   `&Path` as `&[u8]` (spec-side `Seq<u8>`) throughout. The generic
//!   `P: AsRef<Path>` skins of upstream `strip_prefix`/`is_file_name`/
//!   `file_name` (pathutil.rs:96-99, :123, :142-144) are materialized at
//!   the byte form (same declaration family as the glob batch's iterator
//!   materializations).
//! - **memchr face:** `memchr::memchr` / `memrchr` (pathutil.rs:126, :149)
//!   are a trusted one-line face per the harness inventory (section 4);
//!   each call is materialized as an explicit index scan whose contract is
//!   the face characterization (first / last index of the byte, or none)
//!   -- declared per scan.
//! - **Windows arms cut:** per inventory section 9, the `#[cfg(windows)]`
//!   legs (the metadata hidden-attribute checks pathutil.rs:25-36, :62-75)
//!   and the `#[cfg(not(unix))]` deferral arms (:113-116, :129-135,
//!   :165-168) are transcribed as the std-oracle spec face plus platform
//!   axiom records (see the std oracle block below); the verification
//!   target is the unix spelling -- the linux build pin.
//! - **is_hidden_entry deferred:** `is_hidden_entry` (pathutil.rs:56-79)
//!   consumes `crate::walk::DirEntry`; the walk face is IG7's mount, so the
//!   function is carried as a record only (its unix arm is verbatim
//!   `is_hidden_path_only(dent.path())`, pathutil.rs:57-60).
//!
//! DP register entries carried by this file:
//! - **DP33** (pathutil.rs:93-119) -- the unix byte-prefix `strip_prefix`
//!   can cross component boundaries (`/home/foo` strips from `/home/foobar`
//!   with remainder `bar`), while std and the not(unix) arm of the same
//!   upstream function refuse. This file collects the suspects material
//!   chain (counterexample witnesses at both sides + the std oracle
//!   contrast + a cross-platform divergence statement); the batch makes NO
//!   filing (git-parity triage and upstream runtime confirmation are
//!   outstanding). The twin PRESERVES the upstream behavior verbatim.
//! - **DP32, part** (pathutil.rs:157-162 plus the tests-module platform
//!   note pathutil.rs:187-188) -- the file_name dot rules and the
//!   std-divergent trailing-dot family; the twin keeps the byte
//!   semantics (e.g. `file_name("a/")` stays `Some("")`).

use vstd::prelude::*;
use vstd::seq::*;

verus! {

// =========================================================================
// Byte constants and small byte faces
// =========================================================================

/// The path separator byte on unix ('/').
pub open spec const SEP: u8 = 0x2F;
/// The dot byte ('.').
pub open spec const DOT: u8 = 0x2E;

/// exec form of the separator byte ('/').
pub const SEP_EXEC: u8 = 0x2F;
/// exec form of the dot byte ('.').
pub const DOT_EXEC: u8 = 0x2E;

/// `s == [b]` for a one-byte sequence (the exec face of the upstream
/// `name == b"."` comparison site, pathutil.rs:159).
pub open spec fn is_one_byte(s: Seq<u8>, b: u8) -> bool {
    s.len() == 1 && s[0] == b
}

/// `s == [a, b]` for a two-byte sequence (the upstream `name == b".."`
/// comparison site, pathutil.rs:159).
pub open spec fn is_two_bytes(s: Seq<u8>, a: u8, b: u8) -> bool {
    s.len() == 2 && s[0] == a && s[1] == b
}

// =========================================================================
// strip_prefix -- upstream pathutil.rs:93-119 (the DP33 site)
// =========================================================================
//
// Upstream doc (pathutil.rs:93-95, verbatim):
//   "Strip `prefix` from the `path` and return the remainder.
//    If `path` doesn't have a prefix `prefix`, then return `None`."
//
// Origin Rust (pinned tree pathutil.rs:100-111, the cfg(unix) arm, BEFORE
// the PR 3609 patch):
// ```text
//     fn imp<'a>(prefix: &'a Path, path: &'a Path) -> Option<&'a Path> {
//         use std::os::unix::ffi::OsStrExt;
//
//         let prefix = prefix.as_os_str().as_bytes();
//         let path = path.as_os_str().as_bytes();
//         if prefix.len() > path.len() || prefix != &path[0..prefix.len()] {
//             None
//         } else {
//             Some(&Path::new(OsStr::from_bytes(&path[prefix.len()..])))
//         }
//     }
// ```
// The byte-prefix comparison `prefix != &path[0..prefix.len()]` is
// materialized as the element-wise scan `bytes_prefix_eq` below (an index
// comparison over the prefix range; declared here per the materialization
// discipline). The DP33 substance: this is a **raw byte prefix** test --
// it can succeed past a component boundary, which std and the not(unix)
// arm of this very function refuse.
//
// PR 3609 migration (component-boundary fix, both commits, final state
// of the patched verification tree /tmp/pr3609-tree): the unix arm now
// strips the raw byte prefix and then REFUSES the strip when both sides
// of the cut are non-separator bytes ("Don't strip a partial component,
// e.g., '/foo' from '/foobar'"). Patched Origin Rust:
// ```text
//     let rest = path.strip_prefix(prefix)?;
//     if prefix.last().is_some_and(|&b| b != b'/')
//         && rest.first().is_some_and(|&b| b != b'/')
//     {
//         return None;
//     }
//     Some(Path::new(OsStr::from_bytes(rest)))
// ```
// The twin below transcribes this patched semantics line by line: the
// remainder keeps the original raw form INCLUSIVE of the joining
// separator (`strip_prefix("/home/foo", "/home/foo/bar")` still yields
// `Some("/bar")` -- the PR deliberately keeps the unix raw-remainder
// spelling and only rejects the cross-component cuts; verified on the
// patched tree, runtime rows in out/kverus-run/PR3609-verify/).

/// The byte-prefix test `prefix == path[0..prefix.len()]` (the element-wise
/// semantics of the upstream `!=` slice comparison, pathutil.rs:106).
pub open spec fn bytes_prefix_eq(prefix: Seq<u8>, path: Seq<u8>) -> bool {
    prefix.len() <= path.len()
        && forall|i: int| 0 <= i < prefix.len() ==> prefix[i] == path[i]
}

/// exec scan form of `bytes_prefix_eq` (materialization of the `!=`
/// comparison site of pathutil.rs:106).
pub fn bytes_prefix_eq_exec(prefix: &[u8], path: &[u8]) -> (r: bool)
    requires prefix.len() <= path.len(),
    ensures r == bytes_prefix_eq(prefix@, path@)
{
    let mut i = 0usize;
    while i < prefix.len()
        invariant
            0 <= i <= prefix.len(),
            prefix.len() <= path.len(),
            forall|j: int| 0 <= j < i as int ==> prefix@[j] == path@[j],
        decreases prefix.len() - i,
    {
        if prefix[i] == path[i] {
            i += 1;
        } else {
            return false;
        }
    }
    true
}

/// The PR 3609 partial-component cut predicate: the raw byte prefix
/// matched, the prefix is nonempty and does not END in a separator, and
/// the would-be remainder is nonempty and does not START with one --
/// i.e. the cut slices through the interior of a path component (the
/// `prefix.last().is_some_and(|&b| b != b'/') && rest.first().
/// is_some_and(|&b| b != b'/')` guard of the patch, materialized at the
/// byte form).
pub open spec fn crosses_component_boundary(prefix: Seq<u8>, path: Seq<u8>) -> bool {
    prefix.len() > 0
        && path.len() > prefix.len()
        && prefix[prefix.len() - 1] != SEP
        && path[prefix.len() as int] != SEP
}

/// Spec track of the PATCHED unix arm of strip_prefix (the PR 3609
/// final state): the raw byte prefix must match (length test then byte
/// equality) AND the cut must not cross a component boundary; the
/// remainder is the raw byte suffix INCLUDING the joining separator
/// when present (runtime ground truth on the patched tree:
/// `strip_prefix("/home/foo", "/home/foo/bar")` still yields
/// `Some("/bar")`, while `strip_prefix("/home/foo", "/home/foobar")`
/// now yields `None`).
pub open spec fn strip_prefix_spec(prefix: Seq<u8>, path: Seq<u8>) -> Option<Seq<u8>> {
    if prefix.len() > path.len() || !bytes_prefix_eq(prefix, path) {
        None
    } else if crosses_component_boundary(prefix, path) {
        // Don't strip a partial component, e.g., "/foo" from "/foobar".
        None
    } else {
        Some(path.subrange(prefix.len() as int, path.len() as int))
    }
}

/// Spec track of the PRE-patch unix arm (the raw byte strip, kept as a
/// named face for the boundary-domain equivalence statement below and
/// for the historical DP33 ledger: the pinned 0.4.34 behavior that the
/// dp33 material chain was filed against).
pub open spec fn strip_prefix_raw_spec(prefix: Seq<u8>, path: Seq<u8>) -> Option<Seq<u8>> {
    if prefix.len() > path.len() || !bytes_prefix_eq(prefix, path) {
        None
    } else {
        Some(path.subrange(prefix.len() as int, path.len() as int))
    }
}

/// Origin Rust (patched pathutil.rs, cfg(unix) arm, PR 3609 final
/// state) -- transcribed verbatim at the byte form; returns the
/// borrowed remainder of `path`. (The lifetimes of `prefix` and `path`
/// are split here -- upstream uses one `'a` for both, which is fine for
/// its call sites but would pin the returned borrow to the prefix owner;
/// behavior-identical widening made by IG3.)
pub fn strip_prefix<'p, 'a>(prefix: &'p [u8], path: &'a [u8]) -> (r: Option<&'a [u8]>)
    ensures
        (r matches None) == (strip_prefix_spec(prefix@, path@) matches None),
        r matches Some(rest) ==> (strip_prefix_spec(prefix@, path@) matches Some(s) && rest@ == s),
{
    // let rest = path.strip_prefix(prefix)?;
    // (the pre-check materialization of the slice strip: length test
    // then byte equality -- the materialized sites of the pinned arm)
    if prefix.len() > path.len() {
        return None;
    }
    if !bytes_prefix_eq_exec(prefix, path) {
        return None;
    }
    let rest = &path[prefix.len()..];
    // if prefix.last().is_some_and(|&b| b != b'/')
    //     && rest.first().is_some_and(|&b| b != b'/') { return None; }
    if prefix.len() > 0
        && rest.len() > 0
        && prefix[prefix.len() - 1] != SEP_EXEC
        && rest[0] != SEP_EXEC
    {
        return None;
    }
    proof {
        assert(prefix@.len() == prefix.len() as int);
        assert(path@.len() == path.len() as int);
        let plen = prefix.len() as int;
        assert(rest@ =~= path@.subrange(plen, path@.len() as int));
        assert(rest@.len() == path@.len() - plen);
        assert(rest@.len() > 0 ==> rest@[0] == path@[plen]);
    }
    // Some(Path::new(OsStr::from_bytes(rest)))
    Some(rest)
}

// =========================================================================
// is_file_name -- upstream pathutil.rs:120-136
// =========================================================================
//
// Upstream doc (pathutil.rs:121-122, verbatim):
//   "Returns true if this file path is just a file name. i.e., Its parent
//    is the empty string."
//
// Origin Rust (pathutil.rs:124-128, cfg(unix) arm):
// ```text
//     {
//         memchr::memchr(b'/', path.as_ref().as_os_str().as_encoded_bytes())
//             .is_none()
//     }
// ```

/// Spec track: the path contains no separator byte (pathutil.rs:124-128,
/// the `memchr(b'/', ..).is_none()` decision).
pub open spec fn is_file_name_spec(path: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < path.len() ==> path[i] != SEP
}

/// Origin Rust (pathutil.rs:123-136), unix arm; the memchr first-hit scan
/// is materialized as an early-return loop (the face contract is `the
/// first index of the byte or none`; the short-circuit scan computes the
/// same is-none decision).
pub fn is_file_name(path: &[u8]) -> (r: bool)
    ensures r == is_file_name_spec(path@)
{
    let mut i = 0usize;
    while i < path.len()
        invariant
            0 <= i <= path.len(),
            forall|j: int| 0 <= j < i as int ==> path@[j] != SEP,
        decreases path.len() - i,
    {
        if path[i] == SEP_EXEC {
            return false;
        }
        i += 1;
    }
    true
}

// =========================================================================
// The memchr face (last-occurrence scan) and its spec track
// =========================================================================
//
// The trusted face `memchr::memrchr` (pathutil.rs:149, :155) consumed by
// upstream file_name: the LAST index of the byte in the sequence, or None.
// The face's characterization is transcribed as `memrchr_spec` and the
// materialized exec scan `memrchr_face` is proven against it.

/// Whether the byte occurs anywhere in the sequence.
pub open spec fn memrchr_hit(s: Seq<u8>, c: u8) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == c
}

/// The highest index at or below `from` carrying `c` (the hit precondition
/// is established by the caller; the defensive arm below only exists to
/// keep the recursion total).
pub open spec fn memrchr_last(s: Seq<u8>, from: int, c: u8) -> int
    decreases from + 1
{
    if from < 0 || from >= s.len() {
        0
    } else if s[from] == c {
        from
    } else {
        memrchr_last(s, from - 1, c)
    }
}

/// The memrchr face characterization: the last index of `c`, or None.
pub open spec fn memrchr_spec(s: Seq<u8>, c: u8) -> Option<int> {
    if memrchr_hit(s, c) {
        Some(memrchr_last(s, s.len() - 1, c))
    } else {
        None
    }
}

/// exec scan materializing `memrchr(b'/', path).map(|i| i+1).unwrap_or(0)`
/// (pathutil.rs:155): a last-occurrence tracking loop.
pub fn memrchr_face(s: &[u8], c: u8) -> (r: Option<usize>)
    ensures
        r matches Some(i) ==> (0 <= i < s.len()
            && s[i as int] == c
            && forall|k: int| (i as int) < k < s.len() ==> s[k] != c),
        r matches None ==> (forall|k: int| 0 <= k < s.len() ==> s[k] != c),
{
    let mut i = 0usize;
    let mut last: Option<usize> = None;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            last matches Some(j) ==> (0 <= j < i && s[j as int] == c
                && forall|k: int| (j as int) < k < i as int ==> s[k] != c),
            last matches None ==> (forall|j: int| 0 <= j < i as int ==> s[j] != c),
        decreases s.len() - i,
    {
        if s[i] == c {
            last = Some(i);
        }
        i += 1;
    }
    last
}

/// Bridge lemma (scan -> spec, the Some side): a last-occurrence index
/// observed by the exec scan is exactly `memrchr_spec`.
pub proof fn memrchr_spec_some_bridge(s: Seq<u8>, c: u8, i: int)
    requires
        0 <= i < s.len(),
        s[i] == c,
        forall|k: int| i < k < s.len() ==> s[k] != c,
    ensures memrchr_spec(s, c) == Some(i)
    decreases s.len() - i
{
    // the hit exists
    assert(#[trigger] (0 <= i && i < s.len() && s[i] == c));
    assert(memrchr_hit(s, c));
    // the last hit is i, by downward induction from the top
    memrchr_last_is_bridge(s, c, i, s.len() - 1);
}

/// Downward induction: memrchr_last lands on i.
pub proof fn memrchr_last_is_bridge(s: Seq<u8>, c: u8, i: int, from: int)
    requires
        0 <= i <= from < s.len(),
        s[i] == c,
        forall|k: int| i <= k <= from && s[k] == c ==> k == i,
    ensures memrchr_last(s, from, c) == i
    decreases from - i
{
    if from == i {
        // s[from] == c: the base case
    } else {
        assert(s[from] != c) by {
            assert(s[from] == c ==> from == i);  // contradicts from != i
        }
        assert(i <= from - 1);
        memrchr_last_is_bridge(s, c, i, from - 1);
    }
}

/// Bridge lemma (scan -> spec, the None side).
pub proof fn memrchr_spec_none_bridge(s: Seq<u8>, c: u8)
    requires forall|k: int| 0 <= k < s.len() ==> s[k] != c,
    ensures memrchr_spec(s, c) == None
{
    assert(!memrchr_hit(s, c)) by {
        assert forall|i: int| 0 <= i < s.len() implies !(s[i] == c) by {}
    }
}

// =========================================================================
// file_name -- upstream pathutil.rs:137-171
// =========================================================================
//
// Upstream doc (pathutil.rs:138-141, verbatim):
//   "The final component of the path, if it is a normal file.
//    If the path terminates in `.`, `..`, or consists solely of a root of
//    prefix, this will return `None`."
//
// Upstream inline comment (pathutil.rs:157-158, verbatim):
//   "Only a final component that is exactly `.` or `..` has no file
//    name. A real name that merely ends in a `.`, like `.foo.`, does."
//
// Origin Rust (pathutil.rs:145-163, cfg(unix) arm):
// ```text
//     fn imp(path: &Path) -> Option<&OsStr> {
//         use std::os::unix::ffi::OsStrExt;
//
//         use memchr::memrchr;
//
//         let path = path.as_os_str().as_bytes();
//         if path.is_empty() {
//             return None;
//         }
//         let last_slash = memrchr(b'/', path).map(|i| i + 1).unwrap_or(0);
//         let name = &path[last_slash..];
//         if name == b"." || name == b".." {
//             return None;
//         }
//         Some(OsStr::from_bytes(name))
//     }
// ```
// Byte-semantics note (ground-truthed on the pinned source): no
// normalization happens -- `file_name("a/")` is `Some("")` (the empty
// final component is returned as-is), unlike std, whose `Path::file_name`
// is None there. The not(unix) arm (pathutil.rs:165-168) defers to
// `Path::file_name` (which additionally normalizes a trailing-dot
// component on Windows; DP32 platform record, not transcribed here).

/// Spec track of the upstream file_name (pathutil.rs:145-163): empty path
/// -> None; otherwise the byte tail after the last '/' is returned, unless
/// it is exactly `.` or `..`.
pub open spec fn file_name_spec(path: Seq<u8>) -> Option<Seq<u8>> {
    if path.len() == 0 {
        None
    } else {
        let last_slash = match memrchr_spec(path, SEP) {
            Some(i) => i + 1,
            None => 0,
        };
        let name = path.subrange(last_slash, path.len() as int);
        if is_one_byte(name, DOT) || is_two_bytes(name, DOT, DOT) {
            None
        } else {
            Some(name)
        }
    }
}

/// Origin Rust (pathutil.rs:142-171), unix arm, byte form. The `.` / `..`
/// comparisons are spelled element-wise (`name == b"."` is a one-byte
/// slice comparison).
pub fn file_name<'a>(path: &'a [u8]) -> (r: Option<&'a [u8]>)
    ensures
        (r matches None) == (file_name_spec(path@) matches None),
        r matches Some(n) ==> (file_name_spec(path@) matches Some(sn) && n@ == sn),
{
    let path_len = path.len();
    // if path.is_empty() { return None; }
    if path_len == 0 {
        proof {
            assert(path@.len() == 0);
        }
        return None;
    }
    // let last_slash = memrchr(b'/', path).map(|i| i + 1).unwrap_or(0);
    let hit = memrchr_face(path, SEP_EXEC);
    let last_slash = match hit {
        Some(i) => i + 1,
        None => 0,
    };
    proof {
        assert(path@.len() == path_len as int);
        match hit {
            Some(i) => {
                assert(0 <= i < path_len);
                assert(path@[i as int] == SEP);
                assert(forall|k: int| (i as int) < k < path_len as int ==> path@[k] != SEP);
                memrchr_spec_some_bridge(path@, SEP, i as int);
                assert(memrchr_spec(path@, SEP) == Some(i as int));
            }
            None => {
                memrchr_spec_none_bridge(path@, SEP);
                assert(memrchr_spec(path@, SEP) == None);
            }
        }
    }
    // let name = &path[last_slash..];
    let name = &path[last_slash..];
    // if name == b"." || name == b".." { return None; }
    if name.len() == 1 && name[0] == DOT_EXEC {
        proof {
            let int_ls = match memrchr_spec(path@, SEP) {
                Some(i) => i + 1,
                None => 0,
            };
            assert(int_ls == last_slash as int);
            assert(name@ == path@.subrange(int_ls, path_len as int));
            assert(is_one_byte(name@, DOT));
        }
        return None;
    }
    if name.len() == 2 && name[0] == DOT_EXEC && name[1] == DOT_EXEC {
        proof {
            let int_ls = match memrchr_spec(path@, SEP) {
                Some(i) => i + 1,
                None => 0,
            };
            assert(int_ls == last_slash as int);
            assert(name@ == path@.subrange(int_ls, path_len as int));
            assert(is_two_bytes(name@, DOT, DOT));
        }
        return None;
    }
    proof {
        let int_ls = match memrchr_spec(path@, SEP) {
            Some(i) => i + 1,
            None => 0,
        };
        assert(int_ls == last_slash as int);
        assert(name@ == path@.subrange(int_ls, path_len as int));
        assert(!is_one_byte(name@, DOT));
        assert(!is_two_bytes(name@, DOT, DOT));
    }
    // Some(OsStr::from_bytes(name))
    Some(name)
}

// =========================================================================
// is_hidden_path / is_hidden_path_only -- upstream pathutil.rs:5-91
// =========================================================================
//
// Upstream doc of is_hidden_path (pathutil.rs:5-18, verbatim):
//   "Returns true if and only if this path is considered to be hidden.
//    # Platform behavior
//    ## Windows
//    This returns true if one of the following is true:
//    * The base name of the path starts with a `.`.
//    * The file attributes have the `HIDDEN` property set.
//    ## All other platforms
//    This only returns true if the base name of the path starts with a `.`."
//
// The twin transcribes the cfg(not(windows)) arm (pathutil.rs:20-23):
// `fn imp(path: &Path) -> bool { is_hidden_path_only(path) }` -- i.e. on
// unix is_hidden_path is exactly is_hidden_path_only. The windows arm
// (pathutil.rs:25-36) is cut per the platform policy; its behavior is
// recorded as the platform axiom-oracle spec `windows_is_hidden_asserts`
// below (an axiom face, never executed by this linux-targeted twin).
//
// Upstream doc of is_hidden_path_only (pathutil.rs:81-84, verbatim):
//   "Returns true if and only if this path is considered to be hidden from
//    only the path itself.
//    This has the same behavior on all platforms."

/// Spec track of upstream is_hidden_path_only (pathutil.rs:85-91): a
/// file name exists and starts with '.', else false.
pub open spec fn is_hidden_path_only_spec(path: Seq<u8>) -> bool {
    match file_name_spec(path) {
        Some(name) => name.len() > 0 && name[0] == DOT,
        None => false,
    }
}

/// Origin Rust (pathutil.rs:85-91), byte form:
/// ```text
///     if let Some(name) = file_name(path) {
///         name.as_encoded_bytes().starts_with(b".")
///     } else {
///         false
///     }
/// ```
pub fn is_hidden_path_only(path: &[u8]) -> (r: bool)
    ensures r == is_hidden_path_only_spec(path@)
{
    match file_name(path) {
        // name.as_encoded_bytes().starts_with(b".")
        Some(name) => {
            proof {
                let sn = file_name_spec(path@);
                assert(sn matches Some(_));
            }
            name.len() > 0 && name[0] == DOT_EXEC
        }
        None => {
            proof {
                assert(file_name_spec(path@) matches None);
            }
            false
        }
    }
}

/// Origin Rust (pathutil.rs:19-39): the cfg(not(windows)) spelling -- the
/// unix arm delegates to is_hidden_path_only, verbatim.
pub fn is_hidden_path(path: &[u8]) -> (r: bool)
    ensures r == is_hidden_path_only_spec(path@)
{
    // fn imp(path: &Path) -> bool { is_hidden_path_only(path) }
    is_hidden_path_only(path)
}

/// Platform axiom-oracle (the windows arm of pathutil.rs:25-36, RECORD
/// ONLY): on windows the result is `metadata-hidden OR
/// is_hidden_path_only`; never executed by this twin (axiom face of the
/// cut platform leg; anchored to the same file as the unix obligation).
pub open spec fn windows_is_hidden_asserts(path: Seq<u8>, attr_hidden: bool) -> bool {
    // `if let Ok(md) = path.metadata() { if is_hidden(md) { return true } }`
    // followed by `is_hidden_path_only(path)`
    attr_hidden || is_hidden_path_only_spec(path)
}

// =========================================================================
// std oracle face -- the not(unix) arm and std `Path::strip_prefix`
// (the DP33 contrast side; TRUSTED FACE)
// =========================================================================
//
// Why a trusted face: the not(unix) arm of upstream strip_prefix
// (pathutil.rs:113-116) is `path.strip_prefix(prefix).ok()` -- std library
// behavior enters as an oracle. The model below is the component
// semantics of `std::path::Components` plus the component-prefix
// acceptance of `Path::strip_prefix`, with runtime ground truth taken on
// the host toolchain (rustc 1.94.0; sessions recorded in
// out/kverus-run/IG1/notes.md):
//   components(".")       = [CurDir]
//   components("./a")     = [CurDir, Normal("a")]       (leading "." kept)
//   components("a/./b")   = [Normal("a"), Normal("b")]  (interior "." dropped)
//   components("/./a")    = [RootDir, Normal("a")]
//   components("/.")      = [RootDir]
//   components("//./")    = [RootDir]
//   components("././a")   = [CurDir, Normal("a")]  (leading "."-run collapses)
//   components("./../a")  = [CurDir, ParentDir, Normal("a")]
//   components("")        = []
// and the strip_prefix rows:
//   strip_prefix("/home/foo", "/home/foobar") = Err
//   strip_prefix("/home/foo", "/home/foo/bar") = Ok("bar")
//   strip_prefix("home/foo", "home/foobar")   = Err
//   strip_prefix("foo", "foobar/baz")          = Err
//   strip_prefix("a", "a//b")                  = Ok("b")
// Materialization: RootDir as the one-byte "/" component, CurDir as the
// one-byte "." component, and ParentDir as the ".." component bytes. The
// Ok-VALUE side of the oracle (which byte slice std returns) is outside
// the face; the acceptance side carries the DP33 contrast.

/// Split the path bytes into raw '/'-pieces (empty pieces kept: the empties
/// come from leading separators, separator runs, and the empty final
/// piece of a trailing separator).
pub open spec fn split_pieces(path: Seq<u8>, i: int, start: int) -> Seq<Seq<u8>>
    decreases path.len() - i
{
    if i < 0 || i >= path.len() {
        seq![path.subrange(start, path.len() as int)]
    } else if path[i] == SEP {
        let head: Seq<Seq<u8>> = seq![path.subrange(start, i)];
        head.add(split_pieces(path, i + 1, i + 1))
    } else {
        split_pieces(path, i + 1, start)
    }
}

/// All raw pieces of the path (empty path -> no pieces).
pub open spec fn pieces_of(path: Seq<u8>) -> Seq<Seq<u8>> {
    if path.len() == 0 {
        Seq::empty()
    } else {
        split_pieces(path, 0, 0)
    }
}

/// The std Components tail scan (std semantics per the probe sessions):
/// empty pieces drop; a "." piece drops UNLESS it sits in the leading run
/// of a RELATIVE path before anything has been yielded (absolute paths
/// yield RootDir first, so their "." pieces always drop); a leading "."
/// run contributes exactly one CurDir.
pub open spec fn std_scan(pieces: Seq<Seq<u8>>, nothing_yielded: bool) -> Seq<Seq<u8>>
    decreases pieces.len()
{
    if pieces.len() == 0 {
        Seq::empty()
    } else {
        let hd = pieces[0];
        let tl = pieces.subrange(1, pieces.len() as int);
        if hd == Seq::empty() {
            // separator run: dropped
            std_scan(tl, nothing_yielded)
        } else if is_one_byte(hd, DOT) {
            if nothing_yielded {
                let head: Seq<Seq<u8>> = seq![hd];
                head.add(std_scan(tl, false))
            } else {
                std_scan(tl, false)
            }
        } else {
            let head: Seq<Seq<u8>> = seq![hd];
            head.add(std_scan(tl, false))
        }
    }
}

/// The std Component model of a path byte sequence (RootDir materialized
/// as the one-byte "/" component; CurDir as "."). TRUSTED FACE (evidence:
/// the host-toolchain probe sessions above).
pub open spec fn std_comps(path: Seq<u8>) -> Seq<Seq<u8>> {
    let pieces = pieces_of(path);
    if pieces.len() == 0 {
        Seq::empty()
    } else if pieces[0] == Seq::empty() {
        // absolute: RootDir then the tail (dots drop once root is yielded)
        let root: Seq<Seq<u8>> = seq![seq![SEP]];
        root.add(std_scan(pieces.subrange(1, pieces.len() as int), false))
    } else {
        std_scan(pieces, true)
    }
}

/// Component-sequence prefix (the core of the std acceptance test).
pub open spec fn comps_prefix(a: Seq<Seq<u8>>, b: Seq<Seq<u8>>) -> bool
    decreases a.len()
{
    a.len() == 0
        || (a.len() <= b.len()
            && (forall|i: int| 0 <= i < a.len() ==> a[i] == b[i]))
}

/// The std `Path::strip_prefix` ACCEPTANCE oracle (TRUSTED FACE): accepted
/// iff the prefix's component sequence is a prefix of the path's. The
/// Ok-value side is outside the face (carried by the probe rows in the
/// notes). This face is also the exact behavior of the upstream
/// not(unix) arm of strip_prefix (pathutil.rs:113-116).
pub open spec fn std_strip_prefix_accepts(prefix: Seq<u8>, path: Seq<u8>) -> bool {
    comps_prefix(std_comps(prefix), std_comps(path))
}


// =========================================================================
// Staged-evaluation helpers for the std oracle rows (spec-concrete
// computation; each is a one-step unfold plus a literal bridge)
// =========================================================================

/// Elementwise-literal bridge: a subrange equal to a spelled run (generic
/// over the element; used for both byte pieces and component lists).
pub proof fn subrange_is_lit<T>(path: Seq<T>, j: int, k: int, lit: Seq<T>)
    requires
        0 <= j <= k <= path.len(),
        lit.len() == k - j,
        forall|t: int| 0 <= t < lit.len() ==> path[j + t] == lit[t],
    ensures path.subrange(j, k) =~= lit
{
    vstd::seq::lemma_seq_subrange_len(path, j, k);
    assert forall|t: int| 0 <= t < lit.len() implies
        path.subrange(j, k)[t] == lit[t] by {
        vstd::seq::lemma_seq_subrange_index(path, j, k, t);
    }
}

/// The pieces_of canonical row for "/home/foo": ["", "home", "foo"].
pub open spec fn home_bytes() -> Seq<u8> {
    seq![('h' as u8), ('o' as u8), ('m' as u8), ('e' as u8)]
}

/// "foo" bytes.
pub open spec fn foo_bytes() -> Seq<u8> {
    seq![('f' as u8), ('o' as u8), ('o' as u8)]
}

/// "foobar" bytes.
pub open spec fn foobar_bytes() -> Seq<u8> {
    seq![('f' as u8), ('o' as u8), ('o' as u8), ('b' as u8),
        ('a' as u8), ('r' as u8)]
}

/// "x" bytes.
pub open spec fn x_bytes() -> Seq<u8> {
    seq![('x' as u8)]
}

/// The root component bytes ("/").
pub open spec fn root_bytes() -> Seq<u8> {
    seq![SEP]
}

pub proof fn pieces_of_home_foo()
    ensures pieces_of(dp33_prefix_bytes())
        =~= seq![Seq::empty(), home_bytes(), foo_bytes()]
{
    let pre = dp33_prefix_bytes();
    subrange_is_lit(pre, 0, 0, Seq::empty());
    subrange_is_lit(pre, 1, 5, home_bytes());
    subrange_is_lit(pre, 6, 9, foo_bytes());
    reveal_with_fuel(split_pieces, 12);
    assert(pieces_of(pre) =~= seq![Seq::empty(), home_bytes(), foo_bytes()]);
}

pub proof fn pieces_of_home_foobar()
    ensures pieces_of(dp33_path_bytes())
        =~= seq![Seq::empty(), home_bytes(), foobar_bytes()]
{
    let pth = dp33_path_bytes();
    subrange_is_lit(pth, 0, 0, Seq::empty());
    subrange_is_lit(pth, 1, 5, home_bytes());
    subrange_is_lit(pth, 6, 12, foobar_bytes());
    reveal_with_fuel(split_pieces, 14);
    assert(pieces_of(pth) =~= seq![Seq::empty(), home_bytes(), foobar_bytes()]);
}

pub proof fn pieces_of_home_foo_x()
    ensures pieces_of(dp33_path_bytes_aligned())
        =~= seq![Seq::empty(), home_bytes(), foo_bytes(), x_bytes()]
{
    let pth = dp33_path_bytes_aligned();
    subrange_is_lit(pth, 0, 0, Seq::empty());
    subrange_is_lit(pth, 1, 5, home_bytes());
    subrange_is_lit(pth, 6, 9, foo_bytes());
    subrange_is_lit(pth, 10, 11, x_bytes());
    reveal_with_fuel(split_pieces, 14);
    assert(pieces_of(pth)
        =~= seq![Seq::empty(), home_bytes(), foo_bytes(), x_bytes()]);
}


// =========================================================================
// Std-oracle row lemmas (general facts derived from the trusted face;
// the harness rows consume them, keeping the per-row proof load to
// index/length steps)
// =========================================================================

/// The SEP-free tail of the piece split collapses to the single final
/// piece (induction over the scan walk).
pub proof fn split_pieces_no_sep_tail(path: Seq<u8>, i: int, start: int)
    requires
        0 <= start <= i <= path.len(),
        forall|k: int| i <= k < path.len() ==> path[k] != SEP,
    ensures
        split_pieces(path, i, start)
            == seq![path.subrange(start, path.len() as int)]
    decreases path.len() - i
{
    if i >= path.len() {
        // base row (no statements needed: the one-step unfold)
    } else {
        split_pieces_no_sep_tail(path, i + 1, start);
    }
}

/// The non-sep WALK: a SEP-free range (cur..i) leaves split_pieces
/// unchanged (chained one-step unfolds; induction).
pub proof fn split_pieces_no_sep_front(path: Seq<u8>, i: int, cur: int, start: int)
    requires
        0 <= start <= cur <= i <= path.len(),
        forall|k: int| cur <= k < i ==> path[k] != SEP,
    ensures
        split_pieces(path, cur, start) == split_pieces(path, i, start)
    decreases i - cur
{
    if cur == i {
        // trivial
    } else {
        reveal_with_fuel(split_pieces, 1);
        split_pieces_no_sep_front(path, i, cur + 1, start);
    }
}

/// The SEP-branch step (one unfold at a separator byte).
pub proof fn split_pieces_sep_step(path: Seq<u8>, i: int, start: int)
    requires
        0 <= start <= i < path.len(),
        path[i] == SEP,
    ensures
        split_pieces(path, i, start)
            == seq![path.subrange(start, i)].add(split_pieces(path, i + 1, i + 1))
{
}

/// The base-case step (i past the end: the final piece).
pub proof fn split_pieces_base_step(path: Seq<u8>, i: int, start: int)
    requires
        0 <= start <= path.len() <= i,
    ensures
        split_pieces(path, i, start) == seq![path.subrange(start, path.len() as int)]
{
}

/// `s.subrange(0, s.len()) == s` (the full-identity bridge).
pub proof fn subrange_all_is(s: Seq<u8>)
    ensures s.subrange(0, s.len() as int) =~= s
{
    subrange_is_lit(s, 0, s.len() as int, s);
}

/// A list of nonempty non-lone-dot pieces scans to itself (std drops
/// nothing from an all-normal list). Extensionality steps go through
/// the add index/len lemmas explicitly.
pub proof fn scan_all_normal(pieces: Seq<Seq<u8>>, nothing_yielded: bool)
    requires
        pieces.len() > 0,
        forall|k: int| 0 <= k < pieces.len() ==>
            pieces[k] != Seq::empty() && !is_one_byte(pieces[k], DOT),
    ensures std_scan(pieces, nothing_yielded) =~= pieces
    decreases pieces.len()
{
    let hd = pieces[0];
    let tl = pieces.subrange(1, pieces.len() as int);
    vstd::seq::lemma_seq_subrange_len(pieces, 1, pieces.len() as int);
    if tl.len() == 0 {
        reveal_with_fuel(std_scan, 1);
        assert(std_scan(tl, false) =~= Seq::empty());
        let head: Seq<Seq<u8>> = seq![hd];
        vstd::seq::lemma_seq_add_len(head, Seq::empty());
        assert(head.add(Seq::empty()).len() == pieces.len());
        assert forall|i: int| 0 <= i < pieces.len() implies
            head.add(Seq::empty())[i] == pieces[i] by {
            vstd::seq::lemma_seq_add_index1(head, Seq::empty(), i);
        }
        assert(head.add(Seq::empty()) =~= pieces);
    } else {
        reveal_with_fuel(std_scan, 1);
        assert forall|k: int| 0 <= k < tl.len() implies
            tl[k] != Seq::empty() && !is_one_byte(tl[k], DOT) by {
            vstd::seq::lemma_seq_subrange_index(pieces, 1, pieces.len() as int, k);
        }
        scan_all_normal(tl, false);
        let head: Seq<Seq<u8>> = seq![hd];
        vstd::seq::lemma_seq_add_len(head, tl);
        assert(head.add(tl).len() == pieces.len()) by {
            assert(head.len() == 1 && tl.len() == pieces.len() - 1);
        }
        assert forall|i: int| 0 <= i < pieces.len() implies
            head.add(tl)[i] == pieces[i] by {
            if i == 0 {
                vstd::seq::lemma_seq_add_index1(head, tl, 0);
            } else {
                vstd::seq::lemma_seq_add_index2(head, tl, i);
            }
        }
        assert(head.add(tl) =~= pieces);
    }
}

/// A relative SEP-free path has exactly one component: itself -- with
/// the lone-`.` exclusion (a relative "." is std's CurDir component, not
/// a Normal one; the components(".") ground-truth row).
pub proof fn std_comps_rel_single(path: Seq<u8>)
    requires
        path.len() > 0,
        forall|k: int| 0 <= k < path.len() ==> path[k] != SEP,
        !(path.len() == 1 && path[0] == DOT),
    ensures std_comps(path) =~= seq![path]
{
    split_pieces_no_sep_tail(path, 0, 0);
    subrange_all_is(path);
    assert(split_pieces(path, 0, 0) =~= seq![path]);
    reveal(pieces_of);
    let pieces = pieces_of(path);
    assert(pieces =~= seq![path]);
    assert(!is_one_byte(path, DOT)) by {
        if is_one_byte(path, DOT) {
            assert(path.len() == 1 && path[0] == DOT);
        }
    }
    assert(field_all_normal(pieces)) by {
        assert(pieces.len() == 1);
        assert(pieces[0] == path);
        assert(path != Seq::empty());
        assert(!is_one_byte(pieces[0], DOT));
    }
    scan_all_normal(pieces, true);
}

/// All-pieces-normal predicate helper (avoids repeating the guard text).
pub open spec fn field_all_normal(pieces: Seq<Seq<u8>>) -> bool {
    forall|k: int| 0 <= k < pieces.len() ==>
        pieces[k] != Seq::empty() && !is_one_byte(pieces[k], DOT)
}

// =========================================================================
// DP33 material chain -- suspects-registry material, NOT a filed finding
// =========================================================================
//
// Upstream behavior (cfg(unix) byte strip, pathutil.rs:100-111) versus
// std / the not(unix) arm (pathutil.rs:113-116 + std::path::Path::
// strip_prefix): a shared BYTE prefix can cross a component boundary; the
// unix arm strips anyway. The theorems below make the divergence
// machine-observed at both sides. No filing decision is made here --
// git-parity triage (what git itself does with sibling roots that share a
// byte prefix) is upstream-tracker work first.

/// `"/home/foo"` as spec bytes (the DP33 witness prefix).
pub open spec fn dp33_prefix_bytes() -> Seq<u8> {
    seq![('/' as u8), ('h' as u8), ('o' as u8), ('m' as u8), ('e' as u8),
        ('/' as u8), ('f' as u8), ('o' as u8), ('o' as u8)]
}

/// `"/home/foobar"` as spec bytes (the DP33 witness path).
pub open spec fn dp33_path_bytes() -> Seq<u8> {
    seq![('/' as u8), ('h' as u8), ('o' as u8), ('m' as u8), ('e' as u8),
        ('/' as u8), ('f' as u8), ('o' as u8), ('o' as u8), ('b' as u8),
        ('a' as u8), ('r' as u8)]
}

/// `"/home/foo/x"` as spec bytes (the component-aligned control path).
pub open spec fn dp33_path_bytes_aligned() -> Seq<u8> {
    dp33_prefix_bytes().add(seq![('/' as u8), ('x' as u8)])
}

/// PR 3609 residue ledger (the DP33 register entry's fix wave): the
/// historical pre-patch unix-arm witness -- the pinned 0.4.34 byte arm
/// used to strip `/home/foo` from `/home/foobar` with remainder `bar`
/// (the cross-component cut) -- is UNSATISFIABLE under the patched
/// spec: the same pair now returns `None` (dp33_unix_arm_witness_
/// under_patch below; runtime ground truth on the patched tree:
/// `ignore::strip_prefix("/home/foo", "/home/foobar") == None`). The
/// raw byte arm's historical behavior stays machine-observed on the
/// raw face (`strip_prefix_raw_spec`) as `dp33_raw_arm_witness`.
///
/// Counterexample witness (unix side, RAW face): the pre-patch
/// byte-prefix arm strips `/home/foo` from `/home/foobar` with
/// remainder `bar` -- the component boundary is crossed silently.
/// Matches the runtime ground truth on the pinned source
/// (`ignore::strip_prefix("/home/foo", "/home/foobar") == Some("bar")`).
pub proof fn dp33_raw_arm_witness()
    ensures strip_prefix_raw_spec(dp33_prefix_bytes(), dp33_path_bytes())
        == Some(seq![('b' as u8), ('a' as u8), ('r' as u8)])
{
    assert(dp33_prefix_bytes().len() == 9);
    assert(dp33_path_bytes().len() == 12);
    assert forall|i: int| 0 <= i < 9 implies
        dp33_prefix_bytes()[i] == dp33_path_bytes()[i] by {
        assert(dp33_prefix_bytes()[0] == dp33_path_bytes()[0]);
        assert(dp33_prefix_bytes()[1] == dp33_path_bytes()[1]);
        assert(dp33_prefix_bytes()[2] == dp33_path_bytes()[2]);
        assert(dp33_prefix_bytes()[3] == dp33_path_bytes()[3]);
        assert(dp33_prefix_bytes()[4] == dp33_path_bytes()[4]);
        assert(dp33_prefix_bytes()[5] == dp33_path_bytes()[5]);
        assert(dp33_prefix_bytes()[6] == dp33_path_bytes()[6]);
        assert(dp33_prefix_bytes()[7] == dp33_path_bytes()[7]);
        assert(dp33_prefix_bytes()[8] == dp33_path_bytes()[8]);
    }
    assert(bytes_prefix_eq(dp33_prefix_bytes(), dp33_path_bytes()));
    assert(dp33_path_bytes().subrange(9, 12) =~= seq![('b' as u8), ('a' as u8), ('r' as u8)]);
}

/// The DP33 witness repaired (unix side, PATCHED face): the same pair
/// that the raw arm cut through (`/home/foo` off `/home/foobar`)
/// returns `None` -- the partial-component cut is refused. The cut
/// predicate is established by inspection (prefix ends `o`, the next
/// path byte is `b`, both non-separators), so the patched spec takes
/// the refusal branch. Runtime ground truth on the patched tree:
/// `ignore::strip_prefix("/home/foo", "/home/foobar") == None` (the
/// PR 3609 unit-test table row 1).
pub proof fn dp33_unix_arm_witness_under_patch()
    ensures strip_prefix_spec(dp33_prefix_bytes(), dp33_path_bytes()) == None
{
    assert(dp33_prefix_bytes().len() == 9);
    assert(dp33_path_bytes().len() == 12);
    assert forall|i: int| 0 <= i < 9 implies
        dp33_prefix_bytes()[i] == dp33_path_bytes()[i] by {
        assert(dp33_prefix_bytes()[0] == dp33_path_bytes()[0]);
        assert(dp33_prefix_bytes()[1] == dp33_path_bytes()[1]);
        assert(dp33_prefix_bytes()[2] == dp33_path_bytes()[2]);
        assert(dp33_prefix_bytes()[3] == dp33_path_bytes()[3]);
        assert(dp33_prefix_bytes()[4] == dp33_path_bytes()[4]);
        assert(dp33_prefix_bytes()[5] == dp33_path_bytes()[5]);
        assert(dp33_prefix_bytes()[6] == dp33_path_bytes()[6]);
        assert(dp33_prefix_bytes()[7] == dp33_path_bytes()[7]);
        assert(dp33_prefix_bytes()[8] == dp33_path_bytes()[8]);
    }
    assert(bytes_prefix_eq(dp33_prefix_bytes(), dp33_path_bytes()));
    // the cut: prefix[8] == 'o' (non-sep), path[9] == 'b' (non-sep)
    assert(dp33_prefix_bytes()[8] != SEP);
    assert(dp33_path_bytes()[9] != SEP);
    assert(crosses_component_boundary(dp33_prefix_bytes(), dp33_path_bytes()));
}

/// Helper: index-uniformity up to `n` (the negation route of the
/// acceptance-complement argument).
pub open spec fn comps_uniform(a: Seq<Seq<u8>>, b: Seq<Seq<u8>>, n: int) -> bool {
    forall|i: int| 0 <= i < n ==> a[i] == b[i]
}

/// Counterexample witness (std / not(unix) arm side): std refuses the same
/// pair -- the component sequences diverge at the last component
/// (`foo` vs `foobar`), so the component-prefix test fails. Matches the
/// runtime ground truth (`Path::strip_prefix` -> Err).
pub proof fn dp33_std_arm_refuses_witness()
    ensures std_strip_prefix_accepts(dp33_prefix_bytes(), dp33_path_bytes()) == false
{
    // std_comps("/home/foo")    = ["/", "home", "foo"]
    // std_comps("/home/foobar") = ["/", "home", "foobar"]
    // The component values are pinned row-wise (atom level: length and
    // index lemmas over Seq::add), not as one nested-seq literal -- the
    // whole-value form is a pathological Z3 shape here.
    // pin the payload constants (probe-p10: scan fuel needs the spelled
    // literals visible; the open-spec-fn indirections alone do not trigger)
    assert(home_bytes() =~= seq![0x68, 0x6F, 0x6D, 0x65]);
    assert(foo_bytes() =~= seq![0x66, 0x6F, 0x6F]);
    assert(foobar_bytes() =~= seq![0x66, 0x6F, 0x6F, 0x62, 0x61, 0x72]);
    assert(root_bytes() =~= seq![SEP]);
    pieces_of_home_foo();
    pieces_of_home_foobar();
    let pa = pieces_of(dp33_prefix_bytes());
    let pb = pieces_of(dp33_path_bytes());
    let tail_a: Seq<Seq<u8>> = seq![home_bytes(), foo_bytes()];
    let tail_b: Seq<Seq<u8>> = seq![home_bytes(), foobar_bytes()];
    subrange_is_lit(pa, 1, 3, tail_a);
    subrange_is_lit(pb, 1, 3, tail_b);
    reveal_with_fuel(std_scan, 6);
    // std_scan of an all-normal tail list is the list itself (both tails
    // are nonempty non-dot components; the general scan_all_normal row)
    assert(field_all_normal(tail_a)) by {
        assert(tail_a.len() == 2);
        assert(tail_a[0] =~= home_bytes() && home_bytes().len() == 4);
        assert(tail_a[1] =~= foo_bytes() && foo_bytes().len() == 3);
    }
    scan_all_normal(tail_a, false);
    assert(field_all_normal(tail_b)) by {
        assert(tail_b.len() == 2);
        assert(tail_b[0] =~= home_bytes() && home_bytes().len() == 4);
        assert(tail_b[1] =~= foobar_bytes() && foobar_bytes().len() == 6);
    }
    scan_all_normal(tail_b, false);
    // std_comps = RootDir ++ scan-tail: index/length rows
    let root_unit: Seq<Seq<u8>> = seq![root_bytes()];
    let a = std_comps(dp33_prefix_bytes());
    let b = std_comps(dp33_path_bytes());
    vstd::seq::lemma_seq_add_len(root_unit, tail_a);
    vstd::seq::lemma_seq_add_len(root_unit, tail_b);
    assert(a.len() == 3);
    assert(b.len() == 3);
    vstd::seq::lemma_seq_add_index1(root_unit, tail_a, 0);
    vstd::seq::lemma_seq_add_index1(root_unit, tail_b, 0);
    vstd::seq::lemma_seq_add_index2(root_unit, tail_a, 1);
    vstd::seq::lemma_seq_add_index2(root_unit, tail_b, 1);
    vstd::seq::lemma_seq_add_index2(root_unit, tail_a, 2);
    vstd::seq::lemma_seq_add_index2(root_unit, tail_b, 2);
    assert(a[0] =~= root_bytes() && b[0] =~= root_bytes());
    assert(a[1] =~= home_bytes() && b[1] =~= home_bytes());
    assert(a[2] =~= foo_bytes());
    assert(b[2] =~= foobar_bytes());
    // comps_prefix(a, b) fails: index 2 (foo vs foobar) breaks the
    // index-uniformity conjunct; the existential is witnessed by i == 2
    assert(!(a[2] =~= b[2]));
    assert(!comps_uniform(a, b, 3));
}

/// The DP33 divergence statement: RETIRED under the PR 3609 patch -- the
/// two arms of the one upstream function no longer disagree on the filed
/// pair. The pre-patch material (raw unix arm strips while the std oracle
/// refuses) remains machine-observed on the raw face via dp33_raw_arm_
/// witness + dp33_std_arm_refuses_witness; the post-patch statement is
/// the agreement below.
///
/// Post-patch arm agreement (the fix's formal confirmation): on the DP33
/// witness pair, the patched cfg(unix) arm AND the std oracle (== the
/// not(unix) arm, pathutil.rs:113-116) BOTH refuse.
pub proof fn dp33_post_patch_agreement_statement()
    ensures
        strip_prefix_spec(dp33_prefix_bytes(), dp33_path_bytes()) == None,
        std_strip_prefix_accepts(dp33_prefix_bytes(), dp33_path_bytes()) == false,
{
    dp33_unix_arm_witness_under_patch();
    dp33_std_arm_refuses_witness();
}

// =========================================================================
// PR 3609 positive theorem family -- the patched semantics' face
// =========================================================================
//
// The fix's formal obligations, beyond the witness repair above:
// (a) the never-crosses invariant (any Some remainder sits at a component
//     boundary -- empty prefix, root-touching cut, empty remainder, or a
//     separator on either side of the cut);
// (b) the boundary-domain equivalence (within the boundary domain the
//     patched spec is byte-identical to the raw spec -- the pre-patch
//     behavior over every legitimately-aligned prefix is preserved, the
//     "no regression" half of the PR);
// (c) the "/" re-peel bridge (gitignore::strip's second peel consumes
//     the raw "/tail" remainder form exactly: a leading-separator
//     remainder re-peels to the bare tail, which is the std face's
//     candidate spelling -- the consumption-chain no-observation-difference
//     lemma; runtime backing: pr3609-strip-driver rows).

/// (a) Never-crosses invariant: whenever the patched strip returns a
/// remainder, the cut sits at a component boundary (the negation of
/// the partial-component cut predicate; spec-side, from the refusal
/// branch of the patched spec).
pub proof fn pr3609_some_implies_boundary(prefix: Seq<u8>, path: Seq<u8>)
    ensures forall|rest: Seq<u8>|
        strip_prefix_spec(prefix, path) == Some(rest)
        ==> !crosses_component_boundary(prefix, path)
{
    // the refusal branch of strip_prefix_spec is exactly the cut
    // predicate; the Some branch is only reachable when it is false
}

/// (b) Boundary-domain equivalence: over inputs whose cut does NOT
/// cross a component boundary, the patched spec equals the raw
/// (pre-patch) spec byte for byte -- both take the same branch (None on
/// length/byte mismatch, Some with the identical raw remainder
/// otherwise). This is the formal "no regression on the aligned
/// domain" statement: every aligned strip that 0.4.34 performed, the
/// patch still performs, with the same remainder bytes.
pub proof fn pr3609_boundary_equivalence(prefix: Seq<u8>, path: Seq<u8>)
    ensures !crosses_component_boundary(prefix, path)
        ==> strip_prefix_spec(prefix, path) == strip_prefix_raw_spec(prefix, path)
{
    reveal(strip_prefix_spec);
    reveal(strip_prefix_raw_spec);
    reveal(crosses_component_boundary);
    reveal(bytes_prefix_eq);
    if prefix.len() > path.len() {
        // both specs: None
    } else if !bytes_prefix_eq(prefix, path) {
        // both specs: None
    } else {
        // bytes match and no cross: the patched refusal branch is
        // unreachable, both return the same raw remainder
    }
}

/// (c) The "/" re-peel bridge (consumption chain, gitignore.rs:300-303):
/// a remainder that starts with the separator -- the patched unix arm's
/// raw spelling on the root-aligned descendants ("/bar") -- re-peels
/// through the same strip face to the bare tail ("bar"), which is the
/// candidate spelling the std component engine yields for the same
/// pair. Hence the raw-remainder/ std-value difference the PR keeps
/// ("/bar" vs std's "bar") is absorbed by the consumer's own second
/// peel: at the consumption-chain end the two spellings coincide.
/// Runtime backing (patched tree driver): strip_prefix("/home/foo",
/// "/home/foo/bar") == Some("/bar"); strip_prefix("/", "/bar") ==
/// Some("bar"); std == Some("bar") on the original pair.
pub proof fn pr3609_slash_repeel_bridge(before: Seq<u8>)
    requires before.len() > 0 && before[0] == SEP
    ensures
        strip_prefix_spec(seq![SEP], before)
            == Some(before.subrange(1, before.len() as int)),
        strip_prefix_raw_spec(seq![SEP], before)
            == Some(before.subrange(1, before.len() as int)),
{
    // prefix "/" ends with the separator: the cut predicate is false
    // vacuously on both faces (the boundary holds via the prefix side),
    // so both specs take the raw-remainder branch
}

/// The PR 3609 unit-test table (patched pathutil.rs
/// strip_prefix_component_boundary), spec rows: every cross-component
/// pair refuses; every boundary row keeps the raw remainder ("". "/",
/// and "/"-ending prefixes vacuous, the aligned cut via the leading
/// separator of the remainder). Backed by the patched-tree driver rows
/// (transcripts/pr3609-strip-driver-20261119.txt).
pub proof fn pr3609_unit_table_rows()
{
    // ("/home/foo", "/home/foobar") == None
    assert(strip_prefix_spec(dp33_prefix_bytes(), dp33_path_bytes()) == None);
    // ("/home/foo", "/home/foo/bar") == Some("/bar")
    assert(strip_prefix_spec(
        dp33_prefix_bytes(),
        dp33_prefix_bytes().add(seq![0x2F, 0x62, 0x61, 0x72]),
    ) == Some(seq![0x2F, 0x62, 0x61, 0x72]));
    // ("/home/foo", "/home/foo") == Some("")
    assert(strip_prefix_spec(
        dp33_prefix_bytes(),
        dp33_prefix_bytes(),
    ) == Some(Seq::empty()));
    // ("/", "/home/foo") == Some("home/foo")
    assert(strip_prefix_spec(seq![SEP], dp33_prefix_bytes()) == Some(
        seq![0x68, 0x6F, 0x6D, 0x65, 0x2F, 0x66, 0x6F, 0x6F]));
    // ("/home/foo/", "/home/foo/bar") == Some("bar")
    assert(strip_prefix_spec(
        dp33_prefix_bytes().add(seq![SEP]),
        dp33_prefix_bytes().add(seq![0x2F, 0x62, 0x61, 0x72]),
    ) == Some(seq![0x62, 0x61, 0x72]));
    // ("", "foo/bar") == Some("foo/bar")
    assert(strip_prefix_spec(Seq::empty(), seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72])
        == Some(seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72]));
}

/// The DP33 sibling NAME family under the patch (the f1 witness fleet,
/// spec rows): every byte-extension of the root by a non-separator
/// refuses -- foo2, foo-build, build-cache and the lone-letter shapes.
pub proof fn pr3609_sibling_family_refused()
{
    // "/x/build" from "/x/build-cache" and "/x/build-cache/out" -> None
    let build_root: Seq<u8> = seq![0x2F, 0x78, 0x2F, 0x62, 0x75, 0x69, 0x6C, 0x64];
    // "/x/build-cache" == build_root ++ "cache"
    let build_cache: Seq<u8> =
        build_root.add(seq![0x63, 0x61, 0x63, 0x68, 0x65]);
    assert(strip_prefix_spec(build_root, build_cache) == None);
    assert(strip_prefix_spec(
        build_root,
        build_cache.add(seq![0x2F, 0x6F, 0x75, 0x74]),
    ) == None);
    // "a" from "abc" -> None (byte prefix of a NAME)
    assert(strip_prefix_spec(seq![0x61], seq![0x61, 0x62, 0x63]) == None);
    // "foo" from "foobar/baz" -> None
    assert(strip_prefix_spec(
        seq![0x66, 0x6F, 0x6F],
        seq![0x66, 0x6F, 0x6F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A],
    ) == None);
}

/// Control group (agreement side): a properly component-aligned suffix
/// strips on BOTH faces. The path `/home/foo/x` (prefix + "/x"): the std
/// oracle accepts (component prefix). The unix arm's *value* difference
/// on the same pair (`Some("/x")`, separator retained) is recorded in the
/// notes from the runtime probes -- the acceptance side is what both arms
/// agree on here.
pub proof fn dp33_control_group_boundary_suffix()
    ensures
        std_strip_prefix_accepts(
            dp33_prefix_bytes(),
            dp33_path_bytes_aligned(),
        ) == true,
{
    // std_comps("/home/foo")   = ["/", "home", "foo"]
    // std_comps("/home/foo/x") = ["/", "home", "foo", "x"]
    // (row-wise / atom-level value rows, per the refuses-witness shape)
    // pin the payload constants (probe-p10, same as the refuses witness)
    assert(home_bytes() =~= seq![0x68, 0x6F, 0x6D, 0x65]);
    assert(foo_bytes() =~= seq![0x66, 0x6F, 0x6F]);
    assert(x_bytes() =~= seq![0x78]);
    assert(root_bytes() =~= seq![SEP]);
    pieces_of_home_foo();
    pieces_of_home_foo_x();
    let pa = pieces_of(dp33_prefix_bytes());
    let pb = pieces_of(dp33_path_bytes_aligned());
    let tail_a: Seq<Seq<u8>> = seq![home_bytes(), foo_bytes()];
    let tail_b: Seq<Seq<u8>> = seq![home_bytes(), foo_bytes(), x_bytes()];
    subrange_is_lit(pa, 1, 3, tail_a);
    subrange_is_lit(pb, 1, 4, tail_b);
    reveal_with_fuel(std_scan, 6);
    assert(field_all_normal(tail_a)) by {
        assert(tail_a.len() == 2);
        assert(tail_a[0] =~= home_bytes() && home_bytes().len() == 4);
        assert(tail_a[1] =~= foo_bytes() && foo_bytes().len() == 3);
    }
    scan_all_normal(tail_a, false);
    assert(field_all_normal(tail_b)) by {
        assert(tail_b.len() == 3);
        assert(tail_b[0] =~= home_bytes() && home_bytes().len() == 4);
        assert(tail_b[1] =~= foo_bytes() && foo_bytes().len() == 3);
        assert(tail_b[2] =~= x_bytes() && x_bytes().len() == 1);
    }
    scan_all_normal(tail_b, false);
    let root_unit: Seq<Seq<u8>> = seq![root_bytes()];
    let a = std_comps(dp33_prefix_bytes());
    let b = std_comps(dp33_path_bytes_aligned());
    vstd::seq::lemma_seq_add_len(root_unit, tail_a);
    vstd::seq::lemma_seq_add_len(root_unit, tail_b);
    assert(a.len() == 3);
    assert(b.len() == 4);
    assert forall|i: int| 0 <= i < 3 implies a[i] == b[i] by {
        vstd::seq::lemma_seq_add_index1(root_unit, tail_a, 0);
        vstd::seq::lemma_seq_add_index1(root_unit, tail_b, 0);
        vstd::seq::lemma_seq_add_index2(root_unit, tail_a, 1);
        vstd::seq::lemma_seq_add_index2(root_unit, tail_b, 1);
        vstd::seq::lemma_seq_add_index2(root_unit, tail_a, 2);
        vstd::seq::lemma_seq_add_index2(root_unit, tail_b, 2);
        vstd::seq::lemma_seq_add_index2(root_unit, tail_b, 3);
        assert(a[0] =~= root_bytes() && b[0] =~= root_bytes());
        assert(a[1] =~= home_bytes() && b[1] =~= home_bytes());
        assert(a[2] =~= foo_bytes() && b[2] =~= foo_bytes());
    }
}

/// Unix-arm side of the same control group: the byte arm also strips
/// (Some("/x") -- the separator kept, per the runtime ground truth
/// `strip_prefix("/home/foo", "/home/foo/bar") == Some("/bar")`).
pub proof fn dp33_control_group_unix_arm()
    ensures strip_prefix_spec(
        dp33_prefix_bytes(),
        dp33_path_bytes_aligned(),
    ) == Some(seq![('/' as u8), ('x' as u8)])
{
    assert(dp33_prefix_bytes().len() == 9);
    assert(dp33_path_bytes_aligned().len() == 11);
    assert forall|i: int| 0 <= i < 9 implies
        dp33_prefix_bytes()[i] == dp33_path_bytes_aligned()[i] by {
        assert(dp33_prefix_bytes()[0] == dp33_path_bytes_aligned()[0]);
        assert(dp33_prefix_bytes()[1] == dp33_path_bytes_aligned()[1]);
        assert(dp33_prefix_bytes()[2] == dp33_path_bytes_aligned()[2]);
        assert(dp33_prefix_bytes()[3] == dp33_path_bytes_aligned()[3]);
        assert(dp33_prefix_bytes()[4] == dp33_path_bytes_aligned()[4]);
        assert(dp33_prefix_bytes()[5] == dp33_path_bytes_aligned()[5]);
        assert(dp33_prefix_bytes()[6] == dp33_path_bytes_aligned()[6]);
        assert(dp33_prefix_bytes()[7] == dp33_path_bytes_aligned()[7]);
        assert(dp33_prefix_bytes()[8] == dp33_path_bytes_aligned()[8]);
    }
    assert(bytes_prefix_eq(dp33_prefix_bytes(), dp33_path_bytes_aligned()));
    assert(dp33_path_bytes_aligned().subrange(9, 11) =~= seq![('/' as u8), ('x' as u8)]);
    // the PR 3609 boundary holds via the remainder side (path[9] == '/')
    assert(!crosses_component_boundary(dp33_prefix_bytes(), dp33_path_bytes_aligned()));
}

}
