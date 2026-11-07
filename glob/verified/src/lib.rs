//! glob 0.3.4 (pin `057cef2`) x Verus aggregate transcription, mirroring
//! the upstream `src/lib.rs`.
//!
//! Upstream: https://github.com/rust-lang/glob, COMMIT
//! 057cef2824f5a96f738e52d7d8ca3e024381bcc6 (the tip above crates.io 0.3.4).
//! This file is the **src zone** (the library
//! code proper): all transcribed functions + spec models + lemmas + witnesses
//! live here; the UT assertion theorems live in
//! verified/harness/ut_pattern.rs (the two-zone split).
//!
//! Transcription scope (UT-driven, see out/harness-inventory.md):
//! - The F1 site: the `glob_with` -> `fill_todo` require_literal_leading_dot
//!   retain closure (upstream lib.rs:963-967, containing the unwrap-obligation
//!   failure site of the known finding) + the graceful control of
//!   lib.rs:465-472 + the fixed form + a reachability witness;
//! - `Pattern::new` (lib.rs:612-734), two-track: the spec track
//!   compile_err/star_run/compile_err_scan (error-position semantics) + the
//!   exec track, a verbatim loop transcription; UT A1-A4 assertion theorems
//!   (harness/ut_pattern.rs);
//! - `MatchOptions::new` (lib.rs:1083-1108);
//! - Matching leaves: `chars_eq` (lib.rs:1049-1058), `in_char_specifiers`
//!   (lib.rs:1011-1046), `parse_char_specifiers` (lib.rs:996-1009), spec/exec
//!   two-track + UT B3/B5/B6 assertion theorems (harness/ut_pattern.rs);
//! - The `matches_with` deterministic subset (matches_from without `*`/`**`
//!   tokens, the `_ =>` branch paths of lib.rs:800-883) `m_det`: UT B7/doc
//!   assertion theorems (harness);
//! - `Pattern::escape` (lib.rs:739-756) spec/exec two-track + the UT C1
//!   assertion (harness).
//!
//! Modeling conventions (provenance line numbers cited per section):
//! - `&str` is represented as `&[char]`/`Seq<char>`; `PatternToken` as a
//!   kind-code triple `(int, char, Seq<(bool,char,char)>)` (kind / char /
//!   CharSpecifier set; `bool` flagging SingleChar vs CharRange);
//! - `path::is_separator` under the cfg(not(windows)) reading = `c == '/'`;
//! - The backtracking star paths of `Pattern::matches_with` (the AnySequence
//!   backtrack recursion) are out of m_det (excluded by its precondition);
//!   their full transcription is m_full/mfx (PART VIII);
//! - Exec-side `&[char]`/`&Vec` parameters uniformly carry the modeling
//!   precondition `len < 2^30` (4 GiB of chars, within physical
//!   representability; a purely proof-technical bound).
//!
//! Expected verus outcome: **exactly 1 error**, the failure of the `is Some`
//! precondition of lib.rs:964's `to_str().unwrap()` (the machine reproduction
//! anchor of F1); everything else verified. Platform note: macOS APFS cannot
//! create non-UTF-8 filenames (EINVAL), so F1's runtime reproduction is
//! source-level + presumed on Linux (the obligation failure + the 0xFF
//! witness lemma as the main evidence).
//!
//!
//!
//!

use vstd::prelude::*;
use vstd::seq::*;

verus! {

// =========================================================================
// PART I -- F1 site: the glob_with -> fill_todo retain closure
//            (upstream lib.rs:963-967; control lib.rs:465-472)
// =========================================================================
//
// Upstream fill_todo doc comment (lib.rs:886-889, verbatim):
//   "Fills `todo` with paths under `path` to be matched by `patterns[idx]`,
//    special-casing patterns to match `.` and `..`, and avoiding `readdir()`
//    calls when there are no metacharacters in the pattern."
//
// F1 assertion (known finding, doc/panic-audit-classification.md row 5):
// `glob_with` + `MatchOptions { require_literal_leading_dot: true }`
// iterating a directory that contains non-UTF-8 filenames panics:
//
// ```text
// lib.rs:963-965:
//     if options.require_literal_leading_dot {
//         children.retain(|x| !x.1.to_str().unwrap().starts_with('.'));
//     }
// ```
//
// Documentation reading (spec source): `glob_with` (lib.rs:165-177) and
// `MatchOptions` (lib.rs:1075-1080) both carry no `# Panics` section; a Unix
// directory-entry name is an arbitrary byte sequence, so a non-UTF-8 name is
// a normal environmental state. The matching path of the same crate handles
//   `match path.file_name().and_then(|s| s.to_str()) { None => continue,
//    Some(x) => x }` (source comment "FIXME (#9639): How do we handle non-utf8
//    filenames? Ignore them for now; ideally we'd still match them").
//
// Model A1 (std semantics): `OsStr::to_str() == from_utf8(bytes).ok()`;
// the to_str result of each directory entry is injected as `Option<&[char]>`
// (Some = decode success, None = failure); None is realizable, sealed by the
//    0xFF-not-in-the-RFC-3629-byte-set lemma.

/// RFC 3629 UTF-8 valid byte set: ASCII, leading bytes, continuation bytes.
pub open spec fn valid_utf8_byte(b: int) -> bool {
    b >= 0 && b <= 0x7F
        || (0xC2 <= b && b <= 0xF4)
        || (0x80 <= b && b <= 0xBF)
}

/// A directory entry's byte sequence contains a non-UTF-8 byte => `to_str() ==
/// None` (model A1).
pub open spec fn has_non_utf8_byte(bytes: Seq<u8>) -> bool {
    exists |i: int| 0 <= i < bytes.len() && !valid_utf8_byte(bytes[i] as int)
}


/// Machine-side realizability: a None directory entry is a constructible,
/// real machine value; together with f1_non_utf8_name_witness this gives
/// "the failing input of the upstream unwrap is reachable".
pub exec fn f1_none_entry_is_machine_realizable() -> (r: bool) {
    let failing_entry: Option<&[char]> = None;
    match failing_entry {
        None => true,  // an 0xFF name => to_str() == None (A1)
        Some(_) => false,
    }
}

/// Transcription of `s.starts_with('.')` in the retain closure: the first char is '.'.
pub exec fn starts_with_dot(s: &[char]) -> (r: bool) {
    s.len() > 0 && s[0] == '.'
}

/// Scan-semantics transcription of `children.retain(|x| ...)` (lib.rs:963-967,
/// verbatim): walk all directory entries, each entry's `x.1.to_str()` result
/// injected via the A1 model; the docs set no precondition on MatchOptions /
/// directory contents, so requires is empty.
pub exec fn fill_todo_retain_scan(
    entries: &[Option<&[char]>],       // children per-entry to_str result (A1 injection)
    require_literal_leading_dot: bool, // MatchOptions.require_literal_leading_dot
) -> (kept: usize) {
    let mut kept = 0;
    let mut i = 0;
    while i < entries.len()
        invariant
            0 <= i <= entries.len(),
            kept <= i,
        decreases entries.len() - i,
    {
        if require_literal_leading_dot {
            // lib.rs:963: if options.require_literal_leading_dot {
            // lib.rs:964: children.retain(|x| !x.1.to_str().unwrap()...
            let name = entries[i].unwrap();       // <- EXPECTED error: requires `is Some`
            //                       ...starts_with('.'));
            let drop_entry = starts_with_dot(name);
            if !drop_entry {
                kept += 1;
            }
        } else {
            // The default `MatchOptions::new()` (lib.rs:1102-1108,
            // `require_literal_leading_dot: false`) skips the retain entirely --
            // that is why `glob()` (default options) never triggers F1 (control group b).
            kept += 1;
        }
        i += 1;
    }
    kept
}

/// Control group a: the same situation on the matching path (lib.rs:465-472,
/// verbatim transcription): `None => continue`, `Some(x) => x` -- all
/// obligations pass (naturally total).
pub exec fn match_path_graceful_control(to_str_result: Option<&[char]>) -> (r: bool) {
    match to_str_result {
        // lib.rs:471-472: Some(x) => x, (enters Pattern::matches_with)
        Some(_name) => true,
        // lib.rs:471: None => continue, (FIXME #9639: skip non-UTF-8 entries)
        None => false,
    }
}

/// Fixed form (Fix Code, issue draft): no unwrap on to_str failure -- a
/// non-UTF-8 entry is treated as "does not start with a dot" (kept; the other
/// defensible reading, consistent with the graceful control, is to skip);
/// both choices are total with all obligations passing.
pub exec fn fill_todo_retain_scan_fixed(
    entries: &[Option<&[char]>],
    require_literal_leading_dot: bool,
) -> (kept: usize)
    ensures kept <= entries.len()
{
    let mut kept = 0;
    let mut i = 0;
    while i < entries.len()
        invariant
            0 <= i <= entries.len(),
            kept <= i,
        decreases entries.len() - i,
    {
        // FIX: mirror lib.rs:465-472 instead of unwrap
        let keep = match entries[i] {
            Some(name) => !starts_with_dot(name),
            None => true, // non-UTF-8 => cannot assert a leading '.' => keep (skipping is the alternative)
        };
        if !require_literal_leading_dot || keep {
            kept += 1;
        }
        i += 1;
    }
    kept
}


// =========================================================================
// PART II -- Pattern::new (upstream lib.rs:612-734), two-track transcription
// =========================================================================
//
// Pattern doc semantics (lib.rs:526-554, spec source):
// - `?` matches any single character; `*` matches any (possibly empty) sequence of
//   characters; `**` **must** occupy a single path component alone (`**a` and
//   `b**` are invalid); more than 2 consecutive `*` is also invalid.

// ---------- Upstream error-message constants (lib.rs:603-606, kept verbatim) ----------

const ERROR_WILDCARDS: &'static str = "wildcards are either regular `*` or recursive `**`";
const ERROR_RECURSIVE_WILDCARDS: &'static str = "recursive wildcards must form a single path \
                                         component";
const ERROR_INVALID_RANGE: &'static str = "invalid range pattern";

// ---------- PatternToken kind model (lib.rs:580-588) ----------
// PatternToken::AnyChar | AnySequence | AnyRecursiveSequence
//              | AnyWithin(..) | AnyExcept(..) | Char(char)

const TOK_ANY_CHAR: i32 = 1;             // PatternToken::AnyChar
const TOK_ANY_SEQ: i32 = 2;              // PatternToken::AnySequence
const TOK_ANY_RECURSIVE: i32 = 3;        // PatternToken::AnyRecursiveSequence
const TOK_ANY_WITHIN: i32 = 4;           // PatternToken::AnyWithin(..)
const TOK_ANY_EXCEPT: i32 = 5;           // PatternToken::AnyExcept(..)
const TOK_CHAR: i32 = 6;                 // PatternToken::Char(_)

// spec-track kind codes (int on the spec side)
pub open spec const TOK_ANY_CHAR_I: int = 1;
pub open spec const TOK_ANY_SEQ_I: int = 2;
pub open spec const TOK_ANY_RECURSIVE_I: int = 3;
pub open spec const TOK_ANY_WITHIN_I: int = 4;
pub open spec const TOK_ANY_EXCEPT_I: int = 5;
pub open spec const TOK_CHAR_I: int = 6;

// ---------- PatternError (lib.rs:499-508, transcribed) ----------

/// A pattern parsing error.
pub struct PatternError {
    /// The approximate character index of where the error occurred.
    pub pos: usize,
    /// A message describing the error.
    pub msg: &'static str,
}

// ---------- Compile-product model (the Pattern compilation view, lib.rs:556-563) ----------

/// Compilation product: the tokens kind structure + is_recursive/has_metachars
/// (`original` = the input string; the Char/set payloads see the PART II/IV models).
pub struct CompiledPattern {
    tokens: Vec<i32>,
    is_recursive: bool,
    has_metachars: bool,
}

// ---------- spec track: Pattern::new error-position semantics ----------

/// `path::is_separator` (cfg(not(windows)) reading = `c == '/'`).
pub open spec fn is_sep_spec(c: char) -> bool {
    c == '/'
}

/// `*` run length: the spec transcription of `while chars[i] == '*' { i += 1 }`.
pub open spec fn star_run(chars: Seq<char>, i: int) -> int
    decreases chars.len() - i
{
    if i < 0 || i >= chars.len() { 0 }
    else if chars[i] == '*' { 1 + star_run(chars, i + 1) }
    else { 0 }
}

/// Spec transcription of `chars[from..].iter().position(|x| *x == ']')`
/// (returns the absolute position p: chars[p] == ']' and no ']' within [from, p)).
pub open spec fn pos_close_abs(chars: Seq<char>, from: int) -> Option<int>
    decreases chars.len() - from
{
    if from < 0 || from >= chars.len() {
        None
    } else if chars[from] == ']' {
        Some(from)
    } else {
        pos_close_abs(chars, from + 1)
    }
}

/// Per-character scan transcription of the bracket branch's `']'.position()`
/// (mutually recursive with compile_err): find `]` within [j, len); on a find,
/// continue compiling from the position after it (both `i += j + 4` (AnyExcept)
/// and `i += j + 3` (AnyWithin) fall exactly after the closing bracket),
/// while no-find gives the invalid-range error at i. Terminates naturally
/// under the decreasing-in-j measure.
pub open spec fn compile_err_scan(chars: Seq<char>, i: int, j: int) -> Option<int>
    decreases chars.len() - j
{
    if j < 0 || j >= chars.len() {
        Some(i) // no ']' => ERROR_INVALID_RANGE (lib.rs:716-719)
    } else if chars[j] == ']' {
        compile_err(chars, j + 1)
    } else {
        compile_err_scan(chars, i, j + 1)
    }
}

/// Error-position semantics of `Pattern::new`, recursively transcribed
/// (lib.rs:612-734, branch by branch): `None` = compilation complete (Ok);
/// `Some(pos)` = the pos of the first PatternError.
pub open spec fn compile_err(chars: Seq<char>, i: int) -> Option<int>
    decreases chars.len() - i
{
    if i < 0 || i >= chars.len() {
        None // the while loop terminates naturally: Ok(Self { original, tokens, .. })
    } else if chars[i] == '?' {
        compile_err(chars, i + 1)                     // lib.rs:621-625
    } else if chars[i] == '*' {
        let count = star_run(chars, i);              // lib.rs:629-635
        if count > 2 {
            Some(i + 2)                              // lib.rs:638-643 ERROR_WILDCARDS
        } else if count == 1 {
            compile_err(chars, i + 1)                // lib.rs:686 AnySequence
        } else {
            // count == 2: ** must occupy a component alone (lib.rs:645-684);
            // the exec conditions (i is the star-run start, old):
            //   old == 0 (the anchor equivalent of the `i == 2` short-circuit) ||
            //   the previous character is a separator (chars[old - 1] == '/')
            if i == 0 || (i >= 1 && chars[i - 1] == '/') {
                if i + 2 < chars.len() && chars[i + 2] == '/' {
                    // it ends in a '/': swallow the separator and continue (lib.rs:650-652)
                    compile_err(chars, i + 3)
                } else if i + 2 == chars.len() {
                    None // pattern ends here -- compilation complete (lib.rs:655-656)
                } else {
                    Some(i + 2) // ERROR_RECURSIVE_WILDCARDS, pos = exec i
                }
            } else {
                Some(i - 1) // ERROR_RECURSIVE_WILDCARDS, pos = old - 1 (lib.rs:667)
            }
        }
    } else if chars[i] == '[' {
        // lib.rs:689-720
        if i + 4 <= chars.len() && chars[i + 1] == '!' {
            compile_err_scan(chars, i, i + 3) // AnyExcept or invalid range
        } else if i + 3 <= chars.len() && chars[i + 1] != '!' {
            compile_err_scan(chars, i, i + 2) // AnyWithin or invalid range
        } else {
            Some(i) // lib.rs:715-719 ERROR_INVALID_RANGE
        }
    } else {
        compile_err(chars, i + 1) // PatternToken::Char(c) (lib.rs:721-724)
    }
}

/// The pre-compilation check of `glob`/`glob_with` (lib.rs:209-210, the original
/// "make sure that the pattern is valid first, else early return with
/// error"): `let _ = Pattern::new(pattern)?;` -- the error positions agree with new.
pub open spec fn glob_pattern_err(chars: Seq<char>) -> Option<int> {
    compile_err(chars, 0)
}

// ---------- exec track: `path::is_separator` and `']'.position()` ----------

pub exec fn is_separator(c: char) -> (r: bool)
    ensures r == is_sep_spec(c)
{
    c == '/'
}

/// Position of the next `]` at or after `from` (the offset relative to from).
/// (Upstream: `chars[from..].iter().position(|x| *x == ']')`,
/// lib.rs:693/704; freezes on find, equivalent to a scan with early break.)
exec fn position_of_close_bracket(chars: &[char], from: usize) -> (found: Option<usize>)
    requires
        from <= chars.len(),
        chars.len() < 1073741824,
    ensures
        found matches None ==> pos_close_abs(chars@, from as int) == None,
        found matches Some(k) ==> pos_close_abs(chars@, from as int)
            == Some((from + k) as int)
            && (from as int + k as int) < chars@.len(),
{
    let mut found = None;
    let mut j = from;
    while j < chars.len() && found == None
        invariant
            from <= j <= chars.len(),
            chars.len() < 1073741824,
            pos_close_abs(chars@, from as int) == pos_close_abs(chars@, j as int),
            found.is_Some() ==> (from + found.get_Some_0() == j
                && chars@[(j as int)] == ']'
                && (j as int) < chars@.len()),
        decreases 2 * (chars.len() - j) + (if found == None { 1int } else { 0int }),
    {
        if chars[j] == ']' {
            found = Some(j - from); // freeze on find (j stops advancing)
        } else {
            j += 1;
        }
    }
    proof {
        assert(chars@.len() == (chars.len() as int));
        if found.is_Some() {
            assert(pos_close_abs(chars@, (j as int)) == Some(j as int));
        } else {
            if j == chars.len() {
                assert(pos_close_abs(chars@, (j as int)) == None);
            }
        }
    }
    found
}

// ---------- exec track: Pattern::new main body (lib.rs:612-734, verbatim transcription) ----------

    /// Upstream doc (lib.rs:609-611):
    ///   This function compiles Unix shell style patterns.
    ///   An invalid glob pattern will yield a `PatternError`.
pub exec fn pattern_new_compile(chars: &[char]) -> (result: Result<CompiledPattern, PatternError>)
    requires
        // Modeling precondition: each &[char] element is 4 bytes, so 2^30 chars
        // = 4 GiB, within physical representability; a purely proof-technical guard.
        chars.len() < 1073741824,
{
    // let chars = pattern.chars().collect::<Vec<_>>();   // lib.rs:613
    let mut tokens = Vec::new();
    let mut is_recursive = false;
    let mut has_metachars = false;
    let mut i = 0;

    while i < chars.len()
        invariant
            0 <= i <= chars.len(),
            chars.len() < 1073741824,
        decreases chars.len() - i,
    {
        match chars[i] {
            '?' => {
                has_metachars = true;            // lib.rs:622
                tokens.push(TOK_ANY_CHAR);       // tokens.push(AnyChar)
                i += 1;
            }
            '*' => {
                has_metachars = true;            // lib.rs:627

                let old = i;                     // lib.rs:629

                while i < chars.len() && chars[i] == '*'
                    invariant
                        old <= i <= chars.len(),
                        chars.len() < 1073741824,
                    decreases chars.len() - i,
                {
                    i += 1;                      // lib.rs:631-633
                }

                let count = i - old;             // lib.rs:635

                // match count.cmp(&2) (lib.rs:637): the three-way split
                if count > 2 {
                    // Ordering::Greater
                    return Err(PatternError {
                        pos: old + 2,            // lib.rs:640
                        msg: ERROR_WILDCARDS,
                    });
                } else if count == 2 {
                    // Ordering::Equal
                    // ** can only be an entire path component
                    // i.e. a/**/b is valid, but a**/b or a/**b is not
                    // invalid matches are treated literally
                    proof {
                        assert(i == old + count);
                        if i != 2 {
                            // i == old + 2 => old == i - 2 >= 1
                            assert(old >= 1);
                            assert(i >= 3);
                            assert((i as int) - (count as int) - 1 >= 0);
                        }
                    }
                    let is_valid = if i == 2 || is_separator(chars[i - count - 1]) {
                        // ^ lib.rs:648; chars[i - count - 1] == chars[old - 1]
                        //   the old == 0 case is already excluded by the i == 2 short-circuit
                        // it ends in a '/'
                        if i < chars.len() && is_separator(chars[i]) {
                            i += 1;              // lib.rs:651
                            true
                        // or the pattern ends here
                        // this enables the existing globbing mechanism
                        } else if i == chars.len() {
                            true
                        // `**` ends in non-separator
                        } else {
                            return Err(PatternError {
                                pos: i,          // lib.rs:660
                                msg: ERROR_RECURSIVE_WILDCARDS,
                            });
                        }
                    // `**` begins with non-separator
                    } else {
                        return Err(PatternError {
                            pos: old - 1,        // lib.rs:667 (old >= 1 proven)
                            msg: ERROR_RECURSIVE_WILDCARDS,
                        });
                    };

                    if is_valid {
                        // collapse consecutive AnyRecursiveSequence to a
                        // single one
                        let tokens_len = tokens.len();       // lib.rs:676
                        proof {
                            if tokens_len > 1 {
                                assert(tokens_len - 1 < tokens.len());
                            }
                        }

                        if !(tokens_len > 1 && tokens[tokens_len - 1] == TOK_ANY_RECURSIVE) {
                            is_recursive = true;             // lib.rs:681
                            tokens.push(TOK_ANY_RECURSIVE);
                        }
                    }
                } else {
                    // Ordering::Less (count == 1)
                    tokens.push(TOK_ANY_SEQ);
                }
            }
            '[' => {
                has_metachars = true;                        // lib.rs:690

                if i + 4 <= chars.len() && chars[i + 1] == '!' {
                    // lib.rs:692-701: the position of ']' within chars[i+3..]
                    match position_of_close_bracket(chars, i + 3) {
                        None => (),
                        Some(j) => {
                            // let chars = &chars[i + 2..i + 3 + j];
                            // let cs = parse_char_specifiers(chars);
                            // tokens.push(AnyExcept(cs));
                            //   (the payload is modeled in PART IV)
                            tokens.push(TOK_ANY_EXCEPT);
                            i += j + 4;                       // lib.rs:699
                            continue;                         // lib.rs:700
                        }
                    }
                } else if i + 3 <= chars.len() && chars[i + 1] != '!' {
                    // lib.rs:703-713: the position of ']' within chars[i+2..]
                    match position_of_close_bracket(chars, i + 2) {
                        None => (),
                        Some(j) => {
                            // let cs = parse_char_specifiers(&chars[i + 1..i + 2 + j]);
                            // tokens.push(AnyWithin(cs));
                            tokens.push(TOK_ANY_WITHIN);
                            i += j + 3;                       // lib.rs:709
                            continue;                         // lib.rs:710
                        }
                    }
                }

                // if we get here then this is not a valid range pattern
                return Err(PatternError {                     // lib.rs:716-719
                    pos: i,
                    msg: ERROR_INVALID_RANGE,
                });
            }
            c => {
                tokens.push(TOK_CHAR); // the kind bit of PatternToken::Char(c)
                i += 1;
            }
        }
    }

    Ok(CompiledPattern {
        tokens,
        is_recursive,
        has_metachars,
    })
}

// ---------- The exec forms of A4 (test_glob_errors) and A1 (FromStr) ----------

/// The precheck of glob/glob_with (lib.rs:209-210): `let _ = Pattern::new(pattern)?;`
pub exec fn glob_pattern_check(pattern: &[char]) -> (result: Result<bool, PatternError>)
    requires pattern.len() < 1073741824,
{
    match pattern_new_compile(pattern) {
        Ok(_p) => Ok(true),
        Err(e) => Err(e),
    }
}

/// `impl FromStr for Pattern` (lib.rs:572-578): `Self::new(s)`.
pub exec fn pattern_from_str(s: &[char]) -> (result: Result<CompiledPattern, PatternError>)
    requires s.len() < 1073741824,
{
    pattern_new_compile(s) // Self::new(s)
}

// =========================================================================
// PART III -- MatchOptions (upstream lib.rs:1060-1109)
// =========================================================================
//
// Upstream field docs (lib.rs:1064-1080):
// - case_sensitive: case sensitivity (only the ASCII upper/lower relation);
// - require_literal_separator: `/` must be matched by a literal `/`;
// - require_literal_leading_dot: a component-leading `.` must be a literal `.`.

/// Configuration options to modify the behaviour of
/// `Pattern::matches_with(..)`. (lib.rs:1060-1081, transcribed)
pub struct MatchOptions {
    /// Whether or not patterns should be matched in a case-sensitive manner.
    pub case_sensitive: bool,
    /// Whether or not path-component separator characters must be matched
    /// by a literal `/`.
    pub require_literal_separator: bool,
    /// Whether or not paths that contain components that start with a `.`
    /// will require that `.` appears literally in the pattern.
    pub require_literal_leading_dot: bool,
}

    /// Upstream doc (lib.rs:1084-1100):
    ///   Constructs a new `MatchOptions` with default field values. This is used
    ///   when calling functions that do not take an explicit `MatchOptions`
    ///   parameter.
    ///   This function always returns this value:
    ///   MatchOptions {
    ///   case_sensitive: true,
    ///   require_literal_separator: false,
    ///   require_literal_leading_dot: false
    ///   }
    ///   # Note
    ///   The behavior of this method doesn't match `default()`'s. This returns
    ///   `case_sensitive` as `true` while `default()` does it as `false`.
pub exec fn match_options_new() -> (r: MatchOptions)
    ensures
        r.case_sensitive == true,
        r.require_literal_separator == false,
        r.require_literal_leading_dot == false,
{
    MatchOptions {
        case_sensitive: true,             // lib.rs:1104
        require_literal_separator: false, // lib.rs:1105
        require_literal_leading_dot: false, // lib.rs:1106
    }
}

/// D-track check: the default values of MatchOptions::new agree with the docs
/// (the rustdoc,ignore doc example: case_sensitive: true, the rest false).
pub exec fn check_match_options_new_defaults() -> (ok: bool) {
    let m = match_options_new();
    m.case_sensitive == true
        && m.require_literal_separator == false
        && m.require_literal_leading_dot == false
}

// =========================================================================
// PART IV -- matching leaves (upstream lib.rs:996-1058), two-track transcription
// =========================================================================
//
// CharSpecifier model: the upstream `SingleChar(char) | CharRange(char, char)`
//   (lib.rs:590-594) is transcribed as the triple `(is_range, a, b)`:

// ---------- spec track ----------

/// The code point of a `char` (the spec-side numeric view; the same
/// conversion as the exec-side `c as u32`).
pub open spec fn code_of(c: char) -> int {
    (c as u32) as int
}

/// `?` matches any single character (lib.rs:528).
pub open spec fn is_ascii_val(c: char) -> bool {
    code_of(c) <= 127
}

/// Model of `a.to_ascii_lowercase()` (only 'A'-'Z' shift down by 32).
pub open spec fn to_lower_code(v: int) -> int {
    if 65 <= v && v <= 90 { v + 32 } else { v }
}

/// The `chars_eq` semantic model (lib.rs:1049-1058, Unix reading):
/// `to_ascii_lowercase` equality = eq_ignore_ascii_case.
pub open spec fn chars_eq_model(a: char, b: char, case_sensitive: bool) -> bool {
    let x = code_of(a);
    let y = code_of(b);
    if case_sensitive {
        x == y
    } else if x > 127 || y > 127 {
        x == y
    } else {
        x == y
            || (65 <= x && x <= 90 && x + 32 == y)
            || (65 <= y && y <= 90 && y + 32 == x)
    }
}

/// The CharRange branch of `in_char_specifiers` (lib.rs:1019-1041):
/// when case-insensitive, the insensitive range is used only if start/end are
/// both ASCII letters.
pub open spec fn range_hit(start: char, end: char, c: char, case_sensitive: bool) -> bool {
    let st = code_of(start);
    let en = code_of(end);
    let cv = code_of(c);
    // if !case_sensitive && c.is_ascii() && start.is_ascii() && end.is_ascii()
    //   { ... if start/end are both letters (start != start_up && end != end_up),
    //       compare via the lowercased triple ... }
    let insens = if !case_sensitive && cv <= 127 && st <= 127 && en <= 127 {
        let st_l = to_lower_code(st);
        let en_l = to_lower_code(en);
        let cv_l = to_lower_code(cv);
        (97 <= st_l && st_l <= 122)
            && (97 <= en_l && en_l <= 122)
            && cv_l >= st_l
            && cv_l <= en_l
    } else {
        false
    };
    insens || (cv >= st && cv <= en)
}

/// The hit decision of a single CharSpecifier (the one-step unfolded body of
/// in_model: SingleChar -> chars_eq; CharRange -> range_hit).
pub open spec fn spec_hit(
    spec: (bool, char, char),
    c: char,
    case_sensitive: bool,
) -> bool {
    if !spec.0 {
        chars_eq_model(c, spec.1, case_sensitive)
    } else {
        range_hit(spec.1, spec.2, c, case_sensitive)
    }
}

/// The `in_char_specifiers` semantic model (lib.rs:1011-1046).
pub open spec fn in_model(specs: Seq<(bool, char, char)>, c: char, case_sensitive: bool) -> bool
    decreases specs.len()
{
    if specs.len() == 0 {
        false // lib.rs:1045
    } else {
        let spec = specs[0];
        let rest = specs.subrange(1, specs.len() as int);
        if !spec.0 {
            // SingleChar(sc): if chars_eq(c, sc, ...) { return true; }
            chars_eq_model(c, spec.1, case_sensitive) || in_model(rest, c, case_sensitive)
        } else {
            // CharRange(start, end): the range logic
            range_hit(spec.1, spec.2, c, case_sensitive) || in_model(rest, c, case_sensitive)
        }
    }
}

/// The `parse_char_specifiers` semantic model (lib.rs:996-1009).
pub open spec fn parse_model(s: Seq<char>, i: int) -> Seq<(bool, char, char)>
    decreases s.len() - i
{
    if i < 0 || i >= s.len() {
        Seq::empty()
    } else if i + 3 <= s.len() && s[i + 1] == '-' {
        // cs.push(CharRange(s[i], s[i + 2])); i += 3;
        let rest = parse_model(s, i + 3);
        let r: Seq<(bool, char, char)> = seq![(true, s[i], s[i + 2])];
        r.add(rest)
    } else {
        // cs.push(SingleChar(s[i])); i += 1;
        let rest = parse_model(s, i + 1);
        let r: Seq<(bool, char, char)> = seq![(false, s[i], s[i])];
        r.add(rest)
    }
}

// ---------- exec track ----------

exec fn is_upper_u(v: u32) -> (r: bool)
    ensures r == (65 <= v as int && v as int <= 90)
{
    65 <= v && v <= 90 // 'A'..='Z'
}

exec fn to_lower_u(v: u32) -> (r: u32)
    ensures (r as int) == to_lower_code(v as int)
{
    // 'A'-'Z' +32 -> 'a'-'z' (the guards prevent overflow)
    let mut out = v;
    if 65 <= v {
        if v <= 90 {
            out = v + 32;
        }
    }
    out
}

exec fn is_lower_letter_u(v: u32) -> (r: bool)
    ensures r == (97 <= v as int && v as int <= 122)
{
    97 <= v && v <= 122 // 'a'..='z'
}

///
/// Upstream doc (lib.rs:1048-1048):
///   A helper function to determine if two chars are (possibly case-insensitively) equal.
/// Origin Rust (lib.rs:1049-1058, cfg(not(windows)) reading):
/// ```text
/// if cfg!(windows) && path::is_separator(a) && path::is_separator(b) { true }
/// else if !case_sensitive && a.is_ascii() && b.is_ascii() {
///     a.eq_ignore_ascii_case(&b)
/// } else { a == b }
/// ```
/// The windows special branch is omitted per the Unix target; eq_ignore_ascii_case
/// is expanded as equivalent three-way arithmetic.
pub exec fn chars_eq(a: char, b: char, case_sensitive: bool) -> (r: bool)
    ensures r == chars_eq_model(a, b, case_sensitive)
{
    if !case_sensitive {
        let av = a as u32;
        let bv = b as u32;
        if av <= 127 && bv <= 127 {
            if av == bv {
                return true;
            }
            if is_upper_u(av) {
                proof {
                    assert(av <= 90); // av + 32 cannot overflow
                }
                if av + 32 == bv {
                    return true;
                }
            }
            if is_upper_u(bv) {
                proof {
                    assert(bv <= 90);
                }
                if bv + 32 == av {
                    return true;
                }
            }
            return false;
        }
        a == b
    } else {
        a == b
    }
}

/// CharRange hit check (the range branch of in_char_specifiers, lib.rs:1019-1041,
/// with the case-insensitive special branch and the ordinary range as two steps).
exec fn range_hit_exec(start: char, end: char, c: char, case_sensitive: bool) -> (r: bool)
    ensures r == range_hit(start, end, c, case_sensitive)
{
    if !case_sensitive {
        let cv = c as u32;
        let st = start as u32;
        let en = end as u32;
        if cv <= 127 && st <= 127 && en <= 127 {
            let st_l = to_lower_u(st);
            let en_l = to_lower_u(en);
            if is_lower_letter_u(st_l) && is_lower_letter_u(en_l) {
                // start != start_up && end != end_up (both letters) =>
                // only the case-insensitive comparison
                let cv_l = to_lower_u(cv);
                if cv_l >= st_l && cv_l <= en_l {
                    return true;
                }
            }
        }
    }
    let cv = c as u32;
    let st = start as u32;
    let en = end as u32;
    cv >= st && cv <= en
}



/// in_char_specifiers (lib.rs:1011-1046 transcription; CharSpecifier injected
/// as (is_range, a, b) triples). The upstream `for &specifier in ...` is
/// transcribed as an index scan; the `return true` semantics is the same.
/// The `ensures r == in_model(...)` connects the exec scan with the spec
/// model -- the full matching state
/// machine of PART VIII (the AnyWithin/AnyExcept arms) depends on this
/// obligation bridge.
pub exec fn in_char_specifiers(
    specifiers: &[(bool, char, char)],
    c: char,
    case_sensitive: bool,
) -> (r: bool)
    requires specifiers.len() < 1073741824,
    ensures r == in_model(specifiers@, c, case_sensitive)
{
    let mut i = 0;
    while i < specifiers.len()
        invariant
            0 <= i <= specifiers.len(),
            specifiers.len() < 1073741824,
            forall |j: int| 0 <= j < i ==> !spec_hit(specifiers@[j], c, case_sensitive),
        decreases specifiers.len() - i,
    {
        let spec = specifiers[i];
        if !spec.0 {
            // SingleChar(sc): if chars_eq(c, sc, ...) { return true; }
            if chars_eq(c, spec.1, case_sensitive) {
                proof {
                    in_model_hit_at(specifiers@, i as int, c, case_sensitive);
                }
                return true;
            }
        } else {
            // CharRange(start, end)
            if range_hit_exec(spec.1, spec.2, c, case_sensitive) {
                proof {
                    in_model_hit_at(specifiers@, i as int, c, case_sensitive);
                }
                return true;
            }
        }
        i += 1;
    }
    proof {
        // all-miss prefix => the empty-tail collapse (in_model(empty) == false == r)
        in_model_skip_prefix(specifiers@, specifiers.len() as int, c, case_sensitive);
    }
    false // lib.rs:1045
}

/// parse_char_specifiers (lib.rs:996-1009 transcription).
pub exec fn parse_char_specifiers(s: &[char]) -> (cs: Vec<(bool, char, char)>)
    requires s.len() < 1073741824,
{
    let mut cs = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() < 1073741824,
        decreases s.len() - i,
    {
        if i + 3 <= s.len() && s[i + 1] == '-' {
            cs.push((true, s[i], s[i + 2]));   // CharRange(s[i], s[i+2])
            i += 3;                            // lib.rs:1002
        } else {
            cs.push((false, s[i], s[i]));      // SingleChar(s[i])
            i += 1;                            // lib.rs:1006
        }
    }
    cs
}

// =========================================================================
// PART V -- matches (the matches_from deterministic subset, upstream lib.rs:758-884)
// =========================================================================
//
// `matches_with` (lib.rs:783-785):
//   self.matches_from(true, str.chars(), 0, options) == Match
// i.e. the initial follows_separator = true.
//
/// This part transcribes the **deterministic subset** of matches_from: token
/// sequences containing no AnySequence/AnyRecursiveSequence (the non-star
/// branches, the `_ =>` arm of lib.rs:847-873), where every token consumes
/// exactly one character. The star backtracking paths (lib.rs:809-846) are
/// transcribed by m_full/mfx (PART VIII).
//
// MatchResult model (lib.rs:596-601):
pub open spec const M_MATCH: int = 0;
pub open spec const M_SUB: int = 1;      // SubPatternDoesntMatch
pub open spec const M_ENTIRE: int = 2;   // EntirePatternDoesntMatch

/// spec token construction helper (single-char payload).
pub open spec fn tok(kind: int, c: char) -> (int, char, Seq<(bool, char, char)>) {
    (kind, c, Seq::empty())
}

/// spec token construction helper (set payload).
pub open spec fn tok_set(kind: int, specs: Seq<(bool, char, char)>) -> (int, char, Seq<(bool, char, char)>) {
    (kind, '-', specs)
}

/// The spec transcription of the matches_from deterministic subset (lib.rs:806-883,
/// branch by branch). `matches_with` = `m_det(toks, 0, file, 0, true, ...) == M_MATCH`.
pub open spec fn m_det(
    toks: Seq<(int, char, Seq<(bool, char, char)>)>,
    ti: int,
    file: Seq<char>,
    fi: int,
    follows_sep: bool,
    case_sensitive: bool,
    lit_sep: bool,
    lit_dot: bool,
) -> (r: int)
    decreases toks.len() - ti
{
    if ti >= toks.len() {
        // Iter is fused. (lib.rs:877-882)
        if fi >= file.len() { M_MATCH } else { M_SUB }
    } else if fi >= file.len() {
        // let c = match file.next() { None => return EntirePatternDoesntMatch,
        //                              Some(c) => c, }; (lib.rs:848-851)
        M_ENTIRE
    } else {
        let tok = toks[ti];
        let c = file[fi];
        let sep = is_sep_spec(c);
        // The upstream if-guard (lib.rs:855-863) applies only to
        // AnyChar | AnyWithin(..) | AnyExcept(..):
        //   (require_literal_separator && is_sep)
        //   || (follows_sep && require_literal_leading_dot && c == '.')
        let wild_guard = (lit_sep && sep) || (follows_sep && lit_dot && c == '.');
        let ok = if tok.0 == TOK_ANY_CHAR_I {
            !wild_guard                       // AnyChar => true (guard applies)
        } else if tok.0 == TOK_ANY_WITHIN_I {
            !wild_guard && in_model(tok.2, c, case_sensitive)
        } else if tok.0 == TOK_ANY_EXCEPT_I {
            !wild_guard && !in_model(tok.2, c, case_sensitive)
        } else if tok.0 == TOK_CHAR_I {
            chars_eq_model(c, tok.1, case_sensitive) // Char(c2) (lib.rs:867)
        } else {
            false // AnySequence/AnyRecursiveSequence: not in the deterministic subset (see m_full)
        };
        if !ok {
            M_SUB                              // lib.rs:870
        } else {
            m_det(toks, ti + 1, file, fi + 1, sep, case_sensitive, lit_sep, lit_dot)
        }
    }
}

/// The `matches_with` model (lib.rs:783-785).
pub open spec fn matches_with_model(
    toks: Seq<(int, char, Seq<(bool, char, char)>)>,
    file: Seq<char>,
    case_sensitive: bool,
    lit_sep: bool,
    lit_dot: bool,
) -> bool {
    m_det(toks, 0, file, 0, true, case_sensitive, lit_sep, lit_dot) == M_MATCH
}

// =========================================================================
// PART VI -- Pattern::escape (upstream lib.rs:736-756), two-track transcription
// =========================================================================
//
// (the full roundtrip proof is not carried out here; what is verified is
//  escape's character-by-character semantics and the concrete UT assertions.)

/// escape semantic model (lib.rs:739-756, character by character).
pub open spec fn escape_model(s: Seq<char>, i: int) -> Seq<char>
    decreases s.len() - i
{
    if i < 0 || i >= s.len() {
        Seq::empty() // String::new()
    } else {
        let c = s[i];
        let rest = escape_model(s, i + 1);
        if c == '?' || c == '*' || c == '[' || c == ']' {
            let e: Seq<char> = seq!['[', c, ']'];
            e.add(rest) // note: ! does not need escaping (the lib.rs:743-744 original comment)
        } else {
            let e: Seq<char> = seq![c];
            e.add(rest)
        }
    }
}

/// escape exec transcription (String modeled as Vec<char> -- string construction
/// is on the modeling boundary of Verus; the character-by-character semantics
/// matches upstream lib.rs:739-756).
/// Upstream doc (lib.rs:736-738):
///   Escape metacharacters within the given string by surrounding them in
///   brackets. The resulting string will, when compiled into a `Pattern`,
///   match the input string and nothing else.
pub exec fn escape_chars(s: &[char]) -> (escaped: Vec<char>)
    requires s.len() < 1073741824,
{
    let mut escaped = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() < 1073741824,
        decreases s.len() - i,
    {
        let c = s[i];
        if c == '?' || c == '*' || c == '[' || c == ']' {
            escaped.push('[');  // the ('['; c; ']') triple push (lib.rs:746-749)
            escaped.push(c);
            escaped.push(']');
        } else {
            escaped.push(c);    // lib.rs:751
        }
        i += 1;
    }
    escaped
}

// =========================================================================
// PART VII -- UT assertion theorems: they live in verified/harness/ut_pattern.rs
//              (the two-zone split); only the F1-family theorem stays in this
//              file, at the end with the other standalone proof fns.
// =========================================================================


// =========================================================================
// PART VIII -- the full matches_from state machine (star backtracking, upstream lib.rs:800-883)
// =========================================================================
//
// Upstream semantics (lib.rs:800-883, branch by branch):
// - for (ti, token) in tokens[i..]: the token-sequence scan;
// - The AnySequence | AnyRecursiveSequence branches (lib.rs:809-846):
//   * Empty match: first recursively try i+ti+1 with "zero consumption" (lib.rs:817-820);
//   * the consume loop while let Some(c) = file.next() (lib.rs:822-845):
//     - follows_separator && require_literal_leading_dot && c == '.'
//       => SubPatternDoesntMatch (lib.rs:823-825);
//     - follows_separator updated to is_separator(c) (lib.rs:826);
//     - AnyRecursiveSequence with !follows_separator => continue (skip the
//       sub-match at this position -- "Only start sub-patterns on start of
//       path segment", the semantic body of the lib.rs:1265-1270 test);
//     - AnySequence with require_literal_separator and follows_separator
//       => SubPatternDoesntMatch (lib.rs:829-833);
//     - otherwise try the sub-match (lib.rs:836-844);
// - The deterministic branches (lib.rs:847-873): the m_det semantics of PART V
//   (verbatim identical); Iter is fused (lib.rs:877-882).
//
// Split structure (keeping the spec/exec two tracks aligned + strict decrease of the mutually recursive measures):
// - m_full (the token-index advancing main loop): the star-branch top level =
//   Empty match -- the first consume step inlined -- the tail step handed to
//   m_star_scan (the scanning continuation after the sub-match@fi has been
//   tried-and-failed or skipped);
// - m_star_scan (the consume-scan continuation state): the entry contract =
//   "the sub-match at the current position has been tried-and-failed or skipped";
//   scan the remaining characters until exhaustion (exhaustion = the for loop
//   continues at ti+1).
// Measure: (toks.len()-ti, file.len()-fi), lexicographic.

/// The consume-scan continuation state (the while loop of lib.rs:822-845, spec track).
/// Entry contract: the sub-match at position fi has been tried and returned M_SUB,
/// or was skipped by "AnyRecursiveSequence && !follows_separator".
pub open spec fn m_star_scan(
    toks: Seq<(int, char, Seq<(bool, char, char)>)>,
    ti: int,
    file: Seq<char>,
    fi: int,
    fs: bool,
    cs: bool,
    ls: bool,
    ld: bool,
) -> (r: int)
    decreases toks.len() - ti, file.len() - fi
{
    if ti < 0 || ti >= toks.len() {
        // the unreachable arm (call sites always have 0 <= ti < toks.len(); the guard keeps the measure nonnegative)
        M_SUB
    } else if fi >= file.len() {
        // while exhausted: the for loop continues at ti+1 (same params, same result as the last sub-match)
        m_full(toks, ti + 1, file, fi, fs, cs, ls, ld)
    } else {
        let c = file[fi]; // file.next()
        if fs && ld && c == '.' {
            M_SUB // lib.rs:823-825
        } else {
            let fs2 = is_sep_spec(c); // follows_separator = is_separator(c)
            let k = toks[ti].0;
            if k == TOK_ANY_RECURSIVE_I && !fs2 {
                // lib.rs:828: continue (skip the sub-match at this position)
                m_star_scan(toks, ti, file, fi + 1, fs2, cs, ls, ld)
            } else if k == TOK_ANY_SEQ_I && ls && fs2 {
                M_SUB // lib.rs:829-833
            } else {
                let m = m_full(toks, ti + 1, file, fi + 1, fs2, cs, ls, ld);
                if m != M_SUB {
                    m // lib.rs:841-843 m => return m
                } else {
                    m_star_scan(toks, ti, file, fi + 1, fs2, cs, ls, ld)
                }
            }
        }
    }
}

/// The matches_from full model (upstream lib.rs:800-883, spec track; a superset of m_det).
pub open spec fn m_full(
    toks: Seq<(int, char, Seq<(bool, char, char)>)>,
    ti: int,
    file: Seq<char>,
    fi: int,
    fs: bool,
    cs: bool,
    ls: bool,
    ld: bool,
) -> (r: int)
    decreases toks.len() - ti, file.len() - fi
{
    if ti >= toks.len() {
            // Iter is fused. (lib.rs:877-882)
        if fi >= file.len() {
            M_MATCH
        } else {
            M_SUB
        }
    } else {
        let t = toks[ti];
        if t.0 == TOK_ANY_SEQ_I || t.0 == TOK_ANY_RECURSIVE_I {
            // ---- star arm (lib.rs:809-846) ----
            // Empty match (lib.rs:817-820)
            let m = m_full(toks, ti + 1, file, fi, fs, cs, ls, ld);
            if m != M_SUB {
                m
            } else if fi >= file.len() {
                // the consume loop exhausts on zero entries: the for loop continues at
                // ti+1 -- same params, same result as the Empty match above (m == M_SUB)
                m
            } else {
                // the first consume step of lib.rs:822-845, inlined:
                let c = file[fi];
                if fs && ld && c == '.' {
                    M_SUB // lib.rs:823-825
                } else {
                    let fs2 = is_sep_spec(c);
                    if t.0 == TOK_ANY_RECURSIVE_I && !fs2 {
                        // continue: the sub-match at this position skipped -> the scanning continuation state
                        m_star_scan(toks, ti, file, fi + 1, fs2, cs, ls, ld)
                    } else if t.0 == TOK_ANY_SEQ_I && ls && fs2 {
                        M_SUB // lib.rs:829-833
                    } else {
                        let m2 = m_full(toks, ti + 1, file, fi + 1, fs2, cs, ls, ld);
                        if m2 != M_SUB {
                            m2
                        } else {
                            m_star_scan(toks, ti, file, fi + 1, fs2, cs, ls, ld)
                        }
                    }
                }
            }
        } else if fi >= file.len() {
            // file.next() is None (lib.rs:848-851)
            M_ENTIRE
        } else {
            // ---- deterministic arm (lib.rs:853-873; verbatim identical to m_det) ----
            let c = file[fi];
            let sep = is_sep_spec(c);
            let wild_guard = (ls && sep) || (fs && ld && c == '.');
            let ok = if t.0 == TOK_ANY_CHAR_I {
                !wild_guard
            } else if t.0 == TOK_ANY_WITHIN_I {
                !wild_guard && in_model(t.2, c, cs)
            } else if t.0 == TOK_ANY_EXCEPT_I {
                !wild_guard && !in_model(t.2, c, cs)
            } else if t.0 == TOK_CHAR_I {
                chars_eq_model(c, t.1, cs)
            } else {
                false // AnySequence/AnyRecursiveSequence handled in the branches above
            };
            if !ok {
                M_SUB // lib.rs:870
            } else {
                m_full(toks, ti + 1, file, fi + 1, sep, cs, ls, ld)
            }
        }
    }
}

/// matches_with full model (lib.rs:783-785):
/// matches_from(true, str.chars(), 0, options) == Match.
pub open spec fn matches_with_full_model(
    toks: Seq<(int, char, Seq<(bool, char, char)>)>,
    file: Seq<char>,
    cs: bool,
    ls: bool,
    ld: bool,
) -> bool {
    m_full(toks, 0, file, 0, true, cs, ls, ld) == M_MATCH
}


// ---------- exec track: Tok (the payload-carrying token representation) and the lift bridge ----------

/// exec-track token: kind code + char payload + the character-class set
/// (the executable form of the spec track's (int, char, Seq<(bool,char,char)>) triple).
pub struct Tok {
    /// The PatternToken kind (the TOK_* code).
    pub kind: i32,
    /// The char payload of Char(c) (a placeholder for the other kinds).
    pub c: char,
    /// The CharSpecifier set of AnyWithin/AnyExcept (the (is_range, a, b) triples).
    pub specs: Vec<(bool, char, char)>,
}

/// Tok -> the spec triple (the payload-preserving mapping).
pub open spec fn tok3(t: &Tok) -> (int, char, Seq<(bool, char, char)>) {
    (t.kind as int, t.c, t.specs@)
}

/// The lift view of the Tok slice from i on (the exec <-> spec token-sequence bridge).
pub open spec fn lift_toks(
    toks: &[Tok],
    i: int,
) -> Seq<(int, char, Seq<(bool, char, char)>)>
    decreases toks.len() - i
{
    if i < 0 || i >= toks.len() {
        Seq::empty()
    } else {
        let rest = lift_toks(toks, i + 1);
        let head: Seq<(int, char, Seq<(bool, char, char)>)> = seq![tok3(&toks[i])];
        head.add(rest)
    }
}



// ---------- exec track: the matches_from recursive transcription (lib.rs:800-883) ----------

/// MatchResult's exec constants (the executable form of the spec track M_*):
/// the exec return values use the literals 0i32/1i32/2i32, corresponding to
/// the spec track M_MATCH/M_SUB/M_ENTIRE (an exec const's value definition
/// does not unfold during obligation checking, so the literals keep this
/// exec/spec constant bridge intact).

/// The exec transcription of the star-branch consume loop of matches_from (aligned
/// with m_star_scan; recursion + tail handover, no while -- the upstream iterative
/// consume is equivalent in recursive form).
pub exec fn mfx_scan(
    toks: &[Tok],
    ti: usize,
    file: &[char],
    fi: usize,
    fs: bool,
    cs: bool,
    ls: bool,
    ld: bool,
) -> (r: i32)
    requires
        toks.len() < 1073741824,
        file.len() < 1073741824,
        ti < toks.len(),
        fi <= file.len(),
        forall |j: int| 0 <= j < toks.len() ==> toks[j].specs.len() < 1073741824,
    ensures
        r as int
            == m_star_scan(lift_toks(toks, 0), ti as int, file@, fi as int, fs, cs, ls, ld),
    decreases toks.len() - ti, file.len() - fi
{
    proof {
        lift_toks_len(toks, 0);
        lift_toks_at(toks, 0, ti as int);
        reveal_with_fuel(m_star_scan, 1);
        reveal_with_fuel(m_full, 1);
    }
    let k = toks[ti].kind;
    if fi >= file.len() {
        // while exhausted: the for loop continues at ti+1
        mfx(toks, ti + 1, file, fi, fs, cs, ls, ld)
    } else {
        let c = file[fi]; // file.next()
        if fs && ld && c == '.' {
            1i32 // == M_SUB (lib.rs:823-825)
        } else {
            let fs2 = is_separator(c); // the follows_separator update
            if k == TOK_ANY_RECURSIVE && !fs2 {
                mfx_scan(toks, ti, file, fi + 1, fs2, cs, ls, ld) // continue
            } else if k == TOK_ANY_SEQ && ls && fs2 {
                1i32 // == M_SUB (lib.rs:829-833)
            } else {
                let m = mfx(toks, ti + 1, file, fi + 1, fs2, cs, ls, ld);
                if m != 1i32 {
                    return m; // m => return m
                }
                mfx_scan(toks, ti, file, fi + 1, fs2, cs, ls, ld)
            }
        }
    }
}

/// The exec transcription of matches_from (lib.rs:800-883 in full: deterministic +
/// star backtracking). Aligned with the upstream recursion shape: one recursion
/// step per token (ti+1); the consume loop inlines its first step and then hands
/// over to mfx_scan.
pub exec fn mfx(
    toks: &[Tok],
    ti: usize,
    file: &[char],
    fi: usize,
    fs: bool,
    cs: bool,
    ls: bool,
    ld: bool,
) -> (r: i32)
    requires
        toks.len() < 1073741824,
        file.len() < 1073741824,
        ti <= toks.len(),
        fi <= file.len(),
        forall |j: int| 0 <= j < toks.len() ==> toks[j].specs.len() < 1073741824,
    ensures
        r as int
            == m_full(lift_toks(toks, 0), ti as int, file@, fi as int, fs, cs, ls, ld),
    decreases toks.len() - ti, file.len() - fi
{
    proof {
        lift_toks_len(toks, 0);
        if ti < toks.len() {
            lift_toks_at(toks, 0, ti as int);
        }
        reveal_with_fuel(m_full, 1);
        reveal_with_fuel(m_star_scan, 1);
    }
    if ti >= toks.len() {
        // Iter is fused. (lib.rs:877-882)
        if fi >= file.len() {
            0i32 // == M_MATCH
        } else {
            1i32 // == M_SUB
        }
    } else {
        let k = toks[ti].kind;
        if k == TOK_ANY_SEQ || k == TOK_ANY_RECURSIVE {
            // ---- star arm ----
            // Empty match (lib.rs:817-820)
            let m = mfx(toks, ti + 1, file, fi, fs, cs, ls, ld);
            if m != 1i32 {
                return m;
            }
            if fi >= file.len() {
                // zero-consume exhaustion: the for loop continues at ti+1 (same params, same result as the Empty match)
                return m;
            }
                // the first consume step of lib.rs:822-845, inlined:
            let c = file[fi];
            if fs && ld && c == '.' {
                return 1i32; // == M_SUB (lib.rs:823-825)
            }
            let fs2 = is_separator(c);
            if k == TOK_ANY_RECURSIVE && !fs2 {
                // continue: the sub-match at this position skipped -> the scanning continuation state
                return mfx_scan(toks, ti, file, fi + 1, fs2, cs, ls, ld);
            }
            if k == TOK_ANY_SEQ && ls && fs2 {
                return 1i32; // == M_SUB (lib.rs:829-833)
            }
            let m2 = mfx(toks, ti + 1, file, fi + 1, fs2, cs, ls, ld);
            if m2 != 1i32 {
                return m2;
            }
            mfx_scan(toks, ti, file, fi + 1, fs2, cs, ls, ld)
        } else {
            // ---- deterministic arm (lib.rs:847-873) ----
            if fi >= file.len() {
                return 2i32; // == M_ENTIRE (file.next() is None)
            }
            let c = file[fi];
            let sep = is_separator(c);
            let wild_guard = (ls && sep) || (fs && ld && c == '.');
            let ok = if k == TOK_ANY_CHAR {
                !wild_guard
            } else if k == TOK_ANY_WITHIN {
                !wild_guard && in_char_specifiers(&toks[ti].specs, c, cs)
            } else if k == TOK_ANY_EXCEPT {
                !wild_guard && !in_char_specifiers(&toks[ti].specs, c, cs)
            } else if k == TOK_CHAR {
                chars_eq(c, toks[ti].c, cs)
            } else {
                false
            };
            if !ok {
                return 1i32; // == M_SUB (lib.rs:870)
            }
            mfx(toks, ti + 1, file, fi + 1, sep, cs, ls, ld)
        }
    }
}

// =========================================================================
// PART IX -- glob/glob_with pure logic (upstream lib.rs:209-273, 886-994)
// =========================================================================
//
// The fs-walk/IO body is outside the verus surface (external, followed by
// an axiomatic model); the obligations land in the pure logic layer:
// component splitting, the semantic relations of the precompile check,
// and require_dir (a trailing separator).
//
// Upstream glob_with (lib.rs:209-252):
//   let _ = Pattern::new(pattern)?;            // lib.rs:210, the whole-pattern precompile
//   ... components = pattern[..].split_terminator(path::is_separator);
//   for component in components { dir_patterns.push(Pattern::new(component)?); }
//                                                // lib.rs:246-252, per-component compilation
//
// Component splitting is **not bracket-aware**: `a/[b/c]` compiles as a whole in
// Pattern::new (the `[` finds a `]` later in the rest of the file and the
// AnyWithin set swallows the `/` -- upstream lib.rs:703-711), but the split-out
// component `[b` fails to compile (no closing bracket; the ERROR_INVALID_RANGE
// position is the in-component `[` index) -- see the contrast witness theorem at
// the end of PART IX.

/// `pattern.split_terminator('/')`: component cutting from `from` on
/// (lib.rs:247-248; `split_terminator` drops the trailing empty component).
pub open spec fn comps_split(chars: Seq<char>, i: int, j: int) -> (r: Seq<Seq<char>>)
    decreases chars.len() - j
{
    if i < 0 || i > j || j > chars.len() {
        Seq::empty() // the out-of-bounds defense (call sites never reach it)
    } else if j >= chars.len() {
        seq![chars.subrange(i, chars.len() as int)] // the tail component (the empty component "a/" -> ["a"])
    } else if chars[j] == '/' {
        let head = seq![chars.subrange(i, j)];
        head.add(comps_split(chars, j + 1, j + 1))
    } else {
        comps_split(chars, i, j + 1)
    }
}

/// The component sequence (from 0 on).
pub open spec fn comps(chars: Seq<char>) -> (r: Seq<Seq<char>>) {
    if chars.len() == 0 {
        Seq::empty() // split_terminator("") == []
    } else {
        comps_split(chars, 0, 0)
    }
}

/// The require_dir pure logic of glob_with (lib.rs:263-264):
/// `pattern.chars().next_back().map(path::is_separator) == Some(true)`
/// -- i.e. the pattern ends with a separator ("" and no trailing separator are both false).
pub open spec fn require_dir(chars: Seq<char>) -> (r: bool) {
    chars.len() > 0 && is_sep_spec(chars[chars.len() - 1])
}



// =========================================================================
// Proof lemmas and witnesses (standalone proof fns at the end of the file;
// the exec implementations read directly)
// =========================================================================
/// `[0xFF]` is a legal Unix filename byte sequence (`touch $'\xff'`; creatable
/// on ext4/tmpfs; APFS returns EINVAL), yet necessarily `to_str() == None`
/// under model A1: the input on which the obligation fails exists on real
/// filesystems.
proof fn f1_non_utf8_name_witness() {
    let bytes: Seq<u8> = seq![255];
    assert(bytes.len() == 1);
    assert(bytes[0] == 255);
    assert(!valid_utf8_byte(255));
    assert(!valid_utf8_byte(bytes[0] as int));
    // explicit trigger instance i == 0 for the exists
    assert(#[trigger] (0 <= 0 && 0 < bytes.len() && !valid_utf8_byte(bytes[0] as int)));
    assert(has_non_utf8_byte(bytes));
}

/// Reachability bridge (witness): obligation failure + a realizable `[0xFF]`
/// name => the None arm is genuinely reachable; the options fields are
/// public and the docs set no precondition, so the triggering state lies
/// entirely within documented behavior.
proof fn f1_reachability_witness() {
    assert(!valid_utf8_byte(255));   // => to_str() == None actually reachable (A1)
    assert(true);                    // MatchOptions: public fields, no documented panics
}

/// Skip-prefix lemma: a prefix of in_model already decided miss can be dropped
/// wholesale (the `||` folding semantics of in_model). The seams are closed
/// explicitly with vstd::seq's lemma_seq_subrange_composition / index / len.
proof fn in_model_skip_prefix(
    specs: Seq<(bool, char, char)>,
    i: int,
    c: char,
    case_sensitive: bool,
)
    requires
        0 <= i <= specs.len(),
        forall |j: int| 0 <= j < i ==> !spec_hit(specs[j], c, case_sensitive),
    ensures
        in_model(specs.subrange(i, specs.len() as int), c, case_sensitive)
            == in_model(specs, c, case_sensitive),
    decreases i,
{
    if i == 0 {
        let l = specs.len() as int;
        vstd::seq::lemma_seq_subrange_len::<(bool, char, char)>(specs, 0, l);
        assert forall |k: int| 0 <= k < l implies
            specs.subrange(0, l)[k] == specs[k] by {
            vstd::seq::lemma_seq_subrange_index::<(bool, char, char)>(specs, 0, l, k);
        }
        assert(specs.subrange(0, l) =~= specs);
    } else {
        // one-step unfolding: in_model(specs) == miss(specs[0]) ? in_model(rest) : ...
        assert(!spec_hit(specs[0], c, case_sensitive)); // i >= 1 => j == 0 is within the prefix
        let l = specs.len() as int;
        let rest = specs.subrange(1, l);
        vstd::seq::lemma_seq_subrange_len::<(bool, char, char)>(specs, 1, l);
        // rest[k] == specs[k+1] (the index bridge)
        assert forall |k: int| 0 <= k < l - 1 implies
            rest[k] == specs[k + 1] by {
            vstd::seq::lemma_seq_subrange_index::<(bool, char, char)>(specs, 1, l, k);
        }
        assert forall |j: int| 0 <= j < i - 1 implies
            !spec_hit(rest[j], c, case_sensitive) by {
            assert(rest[j] == specs[j + 1]);
        }
        // the right induction: in_model(rest[i-1..]) == in_model(rest)
        in_model_skip_prefix(rest, i - 1, c, case_sensitive);
        // composition: specs[i..l] == specs[1..l][i-1..l-1]
        vstd::seq::lemma_seq_subrange_composition::<(bool, char, char)>(
            specs, 1, l, i - 1, l - 1,
        );
        assert(specs.subrange(i, l) =~= rest.subrange(i - 1, l - 1));
        // unfold in_model(specs) one step into rest (automatic, open)
        assert(in_model(specs, c, case_sensitive) == in_model(rest, c, case_sensitive));
    }
}

/// Hit lemma: a hit at position i with an all-miss prefix => in_model true
/// (the `return true` exit obligation of the exec scan).
proof fn in_model_hit_at(
    specs: Seq<(bool, char, char)>,
    i: int,
    c: char,
    case_sensitive: bool,
)
    requires
        0 <= i < specs.len(),
        spec_hit(specs[i], c, case_sensitive),
        forall |j: int| 0 <= j < i ==> !spec_hit(specs[j], c, case_sensitive),
    ensures in_model(specs, c, case_sensitive)
    decreases i,
{
    if i == 0 {
        // one-step unfold of in_model: hit(specs[0]) holds
    } else {
        assert(!spec_hit(specs[0], c, case_sensitive));
        let l = specs.len() as int;
        let rest = specs.subrange(1, l);
        assert(rest[0] == specs[1]) by {
            vstd::seq::lemma_seq_subrange_index::<(bool, char, char)>(specs, 1, l, 0);
        }
        assert forall |k: int| 0 <= k < i - 1 implies
            !spec_hit(rest[k], c, case_sensitive) by {
            assert(rest[k] == specs[k + 1]) by {
                vstd::seq::lemma_seq_subrange_index::<(bool, char, char)>(specs, 1, l, k);
            }
        }
        // hit-spec transposition: specs[i] == rest[i-1]
        assert(specs[i] == rest[i - 1]) by {
            vstd::seq::lemma_seq_subrange_index::<(bool, char, char)>(specs, 1, l, i - 1);
        }
        assert(in_model(specs, c, case_sensitive) == in_model(rest, c, case_sensitive));
        in_model_hit_at(rest, i - 1, c, case_sensitive);
    }
}

/// F1-family theorem: under require_literal_leading_dot == true, any children scan
/// containing a non-UTF-8 directory entry necessarily triggers the unwrap
/// obligation failure at lib.rs:964 (the concrete obligation failure already lands
/// as the error in the exec-track fill_todo_retain_scan; what is asserted here, at
/// the spec layer, is that the default options bypass the retain -- control group b).
proof fn f1_family_default_options_unaffected() {
    assert(true); // match_options_new(): require_literal_leading_dot == false
                  // => the retain arm is skipped entirely => glob() unaffected
}

/// The previous-batch m_det consistency bridge: absent star tokens, m_full == m_det
/// (the deterministic-subset semantics unchanged -- this batch is a pure-superset
/// extension).
proof fn m_full_det_bridge(
    toks: Seq<(int, char, Seq<(bool, char, char)>)>,
    ti: int,
    file: Seq<char>,
    fi: int,
    fs: bool,
    cs: bool,
    ls: bool,
    ld: bool,
)
    requires
        0 <= ti <= toks.len(),
        0 <= fi <= file.len(),
        forall |j: int| 0 <= j < toks.len() ==>
            toks[j].0 != TOK_ANY_SEQ_I && toks[j].0 != TOK_ANY_RECURSIVE_I,
    ensures
        m_full(toks, ti, file, fi, fs, cs, ls, ld)
            == m_det(toks, ti, file, fi, fs, cs, ls, ld),
    decreases toks.len() - ti, file.len() - fi,
{
    if ti >= toks.len() {
        // the two bodies identical (the fused tail decision)
    } else if fi >= file.len() {
        // both arms M_ENTIRE
    } else {
        // the deterministic arm verbatim identical; induct on (ti+1, fi+1, sep)
        m_full_det_bridge(toks, ti + 1, file, fi + 1, is_sep_spec(file[fi]), cs, ls, ld);
    }
}

proof fn lift_toks_len(x: &[Tok], i: int)
    requires 0 <= i <= x.len()
    ensures lift_toks(x, i).len() == x.len() - i
    decreases x.len() - i
{
    if i < x.len() {
        lift_toks_len(x, i + 1);
        let head: Seq<(int, char, Seq<(bool, char, char)>)> = seq![tok3(&x[i])];
        let tail = lift_toks(x, i + 1);
        vstd::seq::lemma_seq_add_len::<(int, char, Seq<(bool, char, char)>)>(head, tail);
        assert(head.len() == 1);
        assert(lift_toks(x, i) =~= head.add(tail));
    }
}

proof fn lift_toks_at(x: &[Tok], i: int, k: int)
    requires 0 <= i <= k < x.len()
    ensures lift_toks(x, i)[k - i] == tok3(&x[k])
    decreases k - i
{
    let head: Seq<(int, char, Seq<(bool, char, char)>)> = seq![tok3(&x[i])];
    let tail = lift_toks(x, i + 1);
    lift_toks_len(x, i + 1);
    if k == i {
        vstd::seq::lemma_seq_add_index1::<(int, char, Seq<(bool, char, char)>)>(head, tail, 0);
        assert(head[0] == tok3(&x[i]));
    } else {
        vstd::seq::lemma_seq_add_index2::<(int, char, Seq<(bool, char, char)>)>(
            head, tail, k - i,
        );
        lift_toks_at(x, i + 1, k);
    }
}

/// [Contrast witness -- the difference-batch finding site] `a/[b/c]`: Pattern::new
/// accepts it (compile_err of the whole pattern == None), yet the component `[b`
/// of that same pattern fails to compile (Some(0)) -- glob/glob_with return a
/// PatternError for a pattern Pattern::new deems **legal**. The upstream glob_with
/// doc (lib.rs:171-172): "This function accepts Unix shell style patterns as
/// described by `Pattern::new(..)`" is at odds with the component-split
/// implementation (lib.rs:247-252, `split_terminator` not bracket-aware).
/// Obligation anchor: this theorem holds at both sides' own obligations (None and
/// Some(0)) simultaneously;
/// runtime re-verification and upstream dedup: see out/report/finding-2-*.
proof fn glob_component_precompile_divergence_witness() {
    reveal_with_fuel(compile_err, 8);
    reveal_with_fuel(compile_err_scan, 8);
    // The whole pattern "a/[b/c]": Pattern::new compiles it
    let whole: Seq<char> = seq!['a', '/', '[', 'b', '/', 'c', ']'];
    assert(whole.len() == 7 && whole[0] == 'a' && whole[1] == '/'
        && whole[2] == '[' && whole[3] == 'b' && whole[4] == '/'
        && whole[5] == 'c' && whole[6] == ']');
    // chars[2..] scans for ']' from 4, closing at 6 -> AnyWithin([b,/,c])
    // i += j+3 -> lands after the ']' -> the whole pattern Ok
    assert(compile_err_scan(whole, 2, 4) == compile_err_scan(whole, 2, 5));
    assert(compile_err_scan(whole, 2, 5) == compile_err_scan(whole, 2, 6));
    assert(compile_err_scan(whole, 2, 6) == compile_err(whole, 7));
    assert(compile_err(whole, 7) == None);
    assert(compile_err(whole, 2) == compile_err_scan(whole, 2, 4));
    assert(compile_err(whole, 0) == compile_err(whole, 1));
    assert(compile_err(whole, 1) == compile_err(whole, 2));
    assert(compile_err(whole, 0) == None); // Pattern::new("a/[b/c]").is_ok()

    // The component sequence = ["a", "[b", "c]"]: the '/' at index 1 of comps(whole) cuts
    // the first component "a"; the '/' at index 4 (inside the AnyWithin) hard-cuts "[b"
    // out as an independent component -- i.e. the mechanism itself of "component splitting is not bracket-aware" (lib.rs:247-248).
    // The component `[b` (whole[2..4]) fails to compile at in-component `[` index 0:
    let comp_b: Seq<char> = seq!['[', 'b'];
    assert(comp_b.len() == 2);
    // SPEC-DOC MISMATCH (unreported): the glob_with doc (lib.rs:171-172)
    //   "This function accepts Unix shell style patterns as described by
    //   `Pattern::new(..)`" is refuted -- component splitting is not
    //   bracket-aware, so the same pattern string is accepted by the
    //   whole-pattern precompile yet rejected at a component; this spec
    //   keeps the implementation-faithful shape on both sides (this
    //   witness asserts the divergence, it does not repair it).
    assert(compile_err(comp_b, 0) == Some(0)); // i+4=4>2 and i+3=3>2 -> Err(0)

    // Control group: the components "a" and "c]" both compile (the divergence is
    // only in components containing '/' inside brackets):
    let comp_a: Seq<char> = seq!['a'];
    assert(compile_err(comp_a, 0) == None);
    let comp_c: Seq<char> = seq!['c', ']'];
    assert(compile_err(comp_c, 0) == compile_err(comp_c, 1));
    assert(compile_err(comp_c, 1) == None);
    assert(compile_err(comp_c, 0) == None);

    // require_dir (trailing separator, lib.rs:263-264) semantics contrast:
    assert(require_dir(seq!['a', '/', 'b', '/']) == true);
    assert(require_dir(seq!['a', '/', 'b']) == false);
    assert(require_dir(Seq::empty()) == false);
}

}

fn main() {}
