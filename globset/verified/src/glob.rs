//! globset `src/glob.rs` mirror -- GL2 scope: the token layer (Token/
//! GlobOptions, upstream glob.rs:225-286), the Parser state machine
//! (glob.rs:811-1083) and the GlobBuilder::build epilogue error mapping
//! (glob.rs:591-631). The regex lowering (glob.rs:694-809), the strategy
//! extractors (glob.rs:344-589) and the trait faces mount in
//! GL3/GL4/GL8 per out/harness-inventory.md section 6.
//!
//! Upstream pin: crates/globset/src/glob.rs @
//! 178cc027e283fd965cb72d0a7395b219eada170c (code/ read-only).
//!
//! Transcription decisions (see also the crate-root base-mapping table
//! in src/lib.rs):
//!  - Two token carriers. The exec side keeps upstream's `Token` with
//!    `Vec` payloads (`Class.ranges: Vec<(char, char)>`,
//!    `Alternates(Vec<Tokens>)` where `Tokens == Vec<Token>`); the
//!    value side uses `TokenS` with `Seq` payloads (`ranges:
//!    Seq<(char, char)>`, `Alts(Seq<Seq<TokenS>>)`). The two carry the
//!    same lattice; the Seq form is what the spec machine and the KAT
//!    theorem family fold on.
//!  - The `Peekable<Chars>` iterator triple (chars/prev/cur) becomes
//!    the index cursor `pos`: bump advances; peek reads glob[pos];
//!    prev/cur are derived from pos in the value model
//!    (`spec_prev`/`spec_cur` -- upstream's literal fields always equal
//!    these derivations; the exec fields keep the upstream literal
//!    shape and stay in sync via the bump contract). The parse_class
//!    rollback (iterator save/restore) is the pos save/restore.
//!  - `std::path::is_separator` over pattern chars rides the GL1
//!    pinned platform oracle `spec_is_separator` (byte level; chars
//!    outside Latin-1 are never separators on either platform -- the
//!    same closure argument as GL1's pathutil face).
//!  - Error kinds: GL2 owns the five live parse arms; the two
//!    DEPRECATED never-produced variants (GM2/GM3) and the trusted
//!    Regex arm are carried for face completeness (dead-variant family
//!    lemma: `parse_errors_never_dead_variants`).
//!  - The spec machine (the value oracle) and the exec machine (the
//!    safety-verified structural twin) are two faces of the same
//!    lattice: every spec arm below is upstream's arm in upstream's
//!    order, and the exec body below follows the same arms. The ground
//!    truth for the value model is the upstream-run oracle arm
//!    (out/kverus-run/GL2/oracle-run.txt: the pinned upstream glob.rs
//!    copy driven on the 33 syntax + 10 syntaxerr KAT patterns and 38
//!    adversarial probes); the formal exec==spec weave across the two
//!    faces is the registered seam (notes.md W2).

use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::seq::seq;

use crate::pathutil::spec_is_separator;

verus! {

// ===========================================================================
// ErrorKind (upstream lib.rs:164-196; per-variant docs verbatim below;
// the Display/`description` plumbing is GL8's batch).
//
//   /// **DEPRECATED**.
//   ///
//   /// This error used to occur for consistency with git's glob
//   /// specification, but the specification now accepts all uses of
//   /// `**`. When `**` does not appear adjacent to a path separator or
//   /// at the beginning/end of a glob, it is now treated as two
//   /// consecutive `*` patterns. As such, this error is no longer used.
//   ///     (InvalidRecursive, GM2)
//   /// Occurs when a character class (e.g., `[abc]`) is not closed.
//   ///     (UnclosedClass)
//   /// Occurs when a range in a character (e.g., `[a-z]`) is invalid.
//   /// For example, if the range starts with a lexicographically larger
//   /// character than it ends with.    (InvalidRange(char, char))
//   /// Occurs when a `}` is found without a matching `{`.
//   ///     (UnopenedAlternates)
//   /// Occurs when a `{` is found without a matching `}`.
//   ///     (UnclosedAlternates)
//   /// **DEPRECATED**. This error used to occur when an alternating
//   /// group was nested inside another alternating group, e.g.,
//   /// `{{a,b},{c,d}}`. However, this is now supported and as such
//   /// this error cannot occur.    (NestedAlternates, GM3)
//   /// Occurs when an unescaped '\' is found at the end of a glob.
//   ///     (DanglingEscape)
//   /// An error associated with parsing or compiling a regex.  (Regex)
// ===========================================================================

/// The kind of error that can occur when parsing a glob pattern.
/// (Upstream `#[non_exhaustive] enum ErrorKind`, lib.rs:165-196; no
/// std derives on the twin -- the Seq<char> Regex payload is a spec
/// carrier, and datatype equality in the spec positions does not ride
/// std PartialEq.)
pub enum ErrorKind {
    InvalidRecursive,
    UnclosedClass,
    InvalidRange(char, char),
    UnopenedAlternates,
    UnclosedAlternates,
    NestedAlternates,
    DanglingEscape,
    Regex(Seq<char>),
}

/// The five live parse arms (the constructor set of the GL2 machine).
pub open spec fn is_parse_error(k: ErrorKind) -> bool {
    k matches ErrorKind::UnclosedClass || k matches ErrorKind::InvalidRange(_, _)
        || k matches ErrorKind::UnopenedAlternates || k matches ErrorKind::UnclosedAlternates
        || k matches ErrorKind::DanglingEscape
}

/// Family lemma: the parse surface produces no DEPRECATED arm (GM2/GM3,
/// the never-produced promise; upstream CHANGELOG BUGs #373/#1098 killed
/// InvalidRecursive and FEATURE #3048 killed NestedAlternates).
pub proof fn parse_errors_never_dead_variants(k: ErrorKind)
    requires
        is_parse_error(k),
    ensures
        !(k matches ErrorKind::InvalidRecursive),
        !(k matches ErrorKind::NestedAlternates),
        !(k matches ErrorKind::Regex(_)),
{
}

/// The GL2 error value (upstream `Error { glob: Option<String>, kind
/// }`, lib.rs:156-162). The kind column is the GL2-verified face; the
/// pattern-reference column (upstream's
/// `Some(self.glob.to_string())` at every parser site, the error()
/// constructor glob.rs:839-841) rides the caller-visible glob (the
/// caller holds the pattern it passed in) and mounts formally with the
/// Error/ErrorKind plumbing batch (GL8; the deferred ledger records
/// this cut).
pub struct GlobError {
    pub kind: ErrorKind,
}

impl GlobError {
    /// Origin Rust (glob.rs:839-841):
    ///     fn error(&self, kind: ErrorKind) -> Error {
    ///         Error { glob: Some(self.glob.to_string()), kind }
    ///     }
    pub fn error(kind: ErrorKind) -> (r: GlobError)
        ensures
            r.kind == kind,
    {
        GlobError { kind }
    }
}

// ===========================================================================
// GlobOptions (glob.rs:225-256) -- the five-switch bundle.
//
// Upstream field docs (glob.rs:229-243, verbatim): case_insensitive
// "Whether to match case insensitively.", literal_separator "Whether
// to require a literal separator to match a separator in a file path.
// e.g., when enabled, `*` won't match `/`.", backslash_escape "Whether
// or not to use `\` to escape special characters. e.g., when enabled,
// `\*` will match a literal `*`.", empty_alternates "Whether or not an
// empty case in an alternate will be removed. e.g., when enabled,
// `{,a}` will match "" and "a".". allow_unclosed_class "Whether or not
// an unclosed character class is allowed. When an unclosed character
// class is found, the opening `[` is treated as a literal `[`. When
// this isn't enabled, an opening `[` without a corresponding `]` is
// treated as an error."
// ===========================================================================

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct GlobOptions {
    pub case_insensitive: bool,
    pub literal_separator: bool,
    pub backslash_escape: bool,
    pub empty_alternates: bool,
    pub allow_unclosed_class: bool,
}

/// The unix default: `backslash_escape: !is_separator('\\')` = true on
/// the unix axiom set (the host-live reading; glob.rs:246-255).
pub open spec fn spec_opts_unix_default() -> GlobOptions {
    GlobOptions {
        case_insensitive: false,
        literal_separator: false,
        backslash_escape: true,
        empty_alternates: false,
        allow_unclosed_class: false,
    }
}

/// The windows-axiom-set reading of the same default (backslash_escape
/// false there; the D2 oracle dual arm).
pub open spec fn spec_opts_windows_default() -> GlobOptions {
    GlobOptions {
        case_insensitive: false,
        literal_separator: false,
        backslash_escape: false,
        empty_alternates: false,
        allow_unclosed_class: false,
    }
}

/// The platform-parameterized default twin (glob.rs:246-255).
pub fn glob_options_default(windows: bool) -> (o: GlobOptions)
    ensures
        windows ==> o == spec_opts_windows_default(),
        !windows ==> o == spec_opts_unix_default(),
{
    GlobOptions {
        case_insensitive: false,      // glob.rs:249
        literal_separator: false,    // glob.rs:250
        // glob.rs:251: backslash_escape: !is_separator('\\') -- the
        // platform-oracle flip (GL1's is_separator_exec at byte 0x5C)
        backslash_escape: !crate::pathutil::is_separator_exec(0x5c, windows),
        empty_alternates: false,     // glob.rs:252
        allow_unclosed_class: false, // glob.rs:253
    }
}

// ===========================================================================
// Token (glob.rs:258-286; no variant docs upstream -- the crate-level
// Syntax section lib.rs:66-96 is the semantic carrier, quoted in the
// harness notes) and the Seq-payload value twin TokenS.
// ===========================================================================

/// Origin Rust (glob.rs:275-286):
///     enum Token {
///         Literal(char),
///         Any,
///         ZeroOrMore,
///         RecursivePrefix,
///         RecursiveSuffix,
///         RecursiveZeroOrMore,
///         Class { negated: bool, ranges: Vec<(char, char)> },
///         Alternates(Vec<Tokens>),
///     }
/// (struct Tokens(Vec<Token>), glob.rs:258-260, rides Vec<Token>.)
/// (no std derives on the twin: the Alternates(Vec<Vec<Token>>) self
/// reference is an opaque spec carrier; datatype equality in spec
/// positions does not ride std PartialEq, and the exec sites below
/// move and match tokens without PartialEq.)
pub enum Token {
    Literal(char),
    Any,
    ZeroOrMore,
    RecursivePrefix,
    RecursiveSuffix,
    RecursiveZeroOrMore,
    Class {
        negated: bool,
        ranges: Vec<(char, char)>,
    },
    Alternates(Vec<Vec<Token>>),
}

/// The value-side token: the same lattice with Seq payloads (the spec
/// machine's carrier).
pub enum TokenS {
    Lit(char),
    Any,
    Zom,
    RecP,
    RecS,
    RecZ,
    Cls {
        negated: bool,
        ranges: Seq<(char, char)>,
    },
    Alts(Seq<Seq<TokenS>>),
}

// ===========================================================================
// The platform oracle over pattern chars (glob.rs:2/913/929/939/953-955
// call std::path::is_separator on pattern chars; GL1's byte oracle
// projected: chars outside Latin-1 name no separator on either
// platform, closing the char::from ladder the same way pathutil did).
// ===========================================================================

pub open spec fn char_is_sep(c: char, windows: bool) -> bool {
    let b = (c as u32) as int;
    if b > 255 {
        false
    } else {
        spec_is_separator(b as u8, windows)
    }
}

pub fn char_is_sep_exec(c: char, windows: bool) -> (r: bool)
    ensures
        r == char_is_sep(c, windows),
{
    let b = c as u32;
    if b > 255 {
        false
    } else {
        crate::pathutil::is_separator_exec(b as u8, windows)
    }
}

/// Host-live (unix) instantiation of the oracle.
pub open spec fn sep_u(c: char) -> bool {
    char_is_sep(c, false)
}

// ===========================================================================
// THE SPEC VALUE MACHINE -- the functional twin of the parser state
// machine (glob.rs:811-1083). State: chars / pos cursor / branch list /
// alternate stack / unclosed-class latch / options. prev/cur are
// derived from pos (spec_prev/spec_cur). Every arm below is upstream's
// arm in upstream's order; the decision lattice was validated
// row-by-row against the upstream-run oracle arm
// (out/kverus-run/GL2/oracle-run.txt).
//
// All the embedded upstream assert! sites (glob.rs:927, 934, 950, 955,
// 1007, and the last_mut().unwrap() pair at glob.rs:1041,1052) are
// guard-derivable: each one reads back the same char the gating peek
// just observed (the bump-contract identity), or is guarded by the
// first/in_range latch lattice (every non-first class iteration has
// pushed at least one range). The spec machine therefore has no
// dead-branch artifacts; the exec twin re-derives each assert as a
// guard below.
// ===========================================================================

pub struct SState {
    pub chars: Seq<char>,
    pub stack: Seq<int>,    // the alternates_stack (branch indices)
    pub brs: Seq<Seq<TokenS>>,    // the branches (token lists)
    pub pos: int,
    pub unclosed: bool,    // the found_unclosed_class latch
    pub opts: GlobOptions,
}

/// Derived prev (glob.rs:821-822): the char before the last bumped one
/// (None while pos < 2, as upstream's None-initialized pair induces).
pub open spec fn spec_prev(st: SState) -> Option<char> {
    if st.pos < 2 {
        None
    } else {
        Some(st.chars.index(st.pos - 2))
    }
}

/// Derived cur (glob.rs:823-824): the last bumped char (None at pos 0).
pub open spec fn spec_cur(st: SState) -> Option<char> {
    if st.pos == 0 {
        None
    } else {
        Some(st.chars.index(st.pos - 1))
    }
}

/// peek (glob.rs:1080-1082): the next char.
pub open spec fn spec_peek(st: SState) -> Option<char> {
    if st.pos < st.chars.len() {
        Some(st.chars.index(st.pos))
    } else {
        None
    }
}

/// bump (glob.rs:1074-1078): advance the cursor and return the char
/// (None at the end, cursor unchanged -- the iterator's exhaustion).
pub open spec fn spec_bump(st: SState) -> (SState, Option<char>) {
    if st.pos < st.chars.len() {
        let st1 = SState {
            chars: st.chars,
            stack: st.stack,
            brs: st.brs,
            pos: st.pos + 1,
            unclosed: st.unclosed,
            opts: st.opts,
        };
        (st1, Some(st.chars.index(st.pos)))
    } else {
        (st, None)
    }
}

/// push_token (glob.rs:875-880): append to the last branch; the
/// UnopenedAlternates column when the branch list is empty.
pub open spec fn spec_push_token(st: SState, tok: TokenS) -> (SState, Option<ErrorKind>) {
    if st.brs.len() == 0 {
        (st, Some(ErrorKind::UnopenedAlternates))
    } else {
        let st1 = SState {
            chars: st.chars,
            stack: st.stack,
            brs: st.brs.update(st.brs.len() - 1, st.brs.index(st.brs.len() - 1).push(tok)),
            pos: st.pos,
            unclosed: st.unclosed,
            opts: st.opts,
        };
        (st1, None)
    }
}

/// pop_token (glob.rs:882-887): pop the last token of the last branch
/// (the machine only calls it with the branch non-empty; the empty
/// column below is the totality filler, unreachable from the entry
/// state through the machine's own lattice).
pub open spec fn spec_pop_token(st: SState) -> (SState, TokenS) {
    if st.brs.len() > 0 && st.brs.index(st.brs.len() - 1).len() > 0 {
        let last = st.brs.index(st.brs.len() - 1);
        let st1 = SState {
            chars: st.chars,
            stack: st.stack,
            brs: st.brs.update(st.brs.len() - 1, last.subrange(0, last.len() - 1)),
            pos: st.pos,
            unclosed: st.unclosed,
            opts: st.opts,
        };
        (st1, last.index(last.len() - 1))
    } else {
        (st, TokenS::Zom)
    }
}

/// have_tokens (glob.rs:889-894).
pub open spec fn spec_have_tokens(st: SState) -> Result<bool, ErrorKind> {
    if st.brs.len() == 0 {
        Err(ErrorKind::UnopenedAlternates)
    } else {
        Ok(st.brs.index(st.brs.len() - 1).len() > 0)
    }
}

/// push_alternate (glob.rs:859-863): stack.push(brs.len()),
/// branches.push(empty).
pub open spec fn spec_push_alternate(st: SState) -> SState {
    SState {
        chars: st.chars,
        stack: st.stack.push(st.brs.len() as int),
        brs: st.brs.push(Seq::empty()),
        pos: st.pos,
        unclosed: st.unclosed,
        opts: st.opts,
    }
}

/// pop_alternate (glob.rs:865-873):
///   let Some(start) = self.alternates_stack.pop() else
///       { return Err(self.error(ErrorKind::UnopenedAlternates)); };
///   assert!(start <= self.branches.len());
///   let alts = Token::Alternates(self.branches.drain(start..).collect());
///   self.push_token(alts)?;
/// (the assert rides the stack-entry domain: every entry sits in
/// [1, brs.len()] -- push_alternate pushes brs.len() >= 1 and the
/// drain lattice only shrinks above the entries)
pub open spec fn spec_pop_alternate(st: SState) -> (SState, Option<ErrorKind>) {
    if st.stack.len() == 0 {
        (st, Some(ErrorKind::UnopenedAlternates))
    } else {
        let start = st.stack.index(st.stack.len() - 1);
        let alts = TokenS::Alts(st.brs.subrange(start as int, st.brs.len() as int));
        let st2 = SState {
            chars: st.chars,
            stack: st.stack.subrange(0, st.stack.len() - 1),
            brs: st.brs.subrange(0, start as int),
            pos: st.pos,
            unclosed: st.unclosed,
            opts: st.opts,
        };
        spec_push_token(st2, alts)
    }
}

/// parse_comma (glob.rs:896-905), with the upstream comment:
///   // If we aren't inside a group alternation, then don't
///   // treat commas specially. Otherwise, we need to start
///   // a new alternate branch.
pub open spec fn spec_parse_comma(st: SState) -> (SState, Option<ErrorKind>) {
    if st.stack.len() == 0 {
        spec_push_token(st, TokenS::Lit(','))
    } else {
        let st1 = SState {
            chars: st.chars,
            stack: st.stack,
            brs: st.brs.push(Seq::empty()),
            pos: st.pos,
            unclosed: st.unclosed,
            opts: st.opts,
        };
        (st1, None)
    }
}

/// parse_backslash (glob.rs:907-919):
///   if self.opts.backslash_escape {
///       match self.bump() {
///           None => Err(self.error(ErrorKind::DanglingEscape)),
///           Some(c) => self.push_token(Token::Literal(c)),
///       }
///   } else if is_separator('\\') {
///       // Normalize all patterns to use / as a separator.
///       self.push_token(Token::Literal('/'))
///   } else {
///       self.push_token(Token::Literal('\\'))
///   }
/// (the is_separator('\\') arm is oracle-parameterized; the unix oracle
/// takes the else-branch -- Literal('\\'), oracle-run.txt:77.)
pub open spec fn spec_parse_backslash(st: SState, windows: bool) -> (SState, Option<ErrorKind>) {
    if st.opts.backslash_escape {
        let b = spec_bump(st);
        if b.1 is None {
            (st, Some(ErrorKind::DanglingEscape))
        } else {
            spec_push_token(b.0, TokenS::Lit(b.1.get_Some_0()))
        }
    } else if char_is_sep(0x5c as char, windows) {
        // Normalize all patterns to use / as a separator.
        spec_push_token(st, TokenS::Lit('/'))
    } else {
        spec_push_token(st, TokenS::Lit('\\'))
    }
}

// -- parse_class (glob.rs:982-1072) --

/// add_to_last_range (glob.rs:988-1002): set the last range's end to
/// `add`, the InvalidRange(start, add) column when the pair unorders.
pub open spec fn spec_add_to_last(
    st: SState,
    ranges: Seq<(char, char)>,
    add: char,
) -> (Seq<(char, char)>, Option<ErrorKind>) {
    let r = ranges.index(ranges.len() - 1);
    let cand = (r.0, add);
    if cand.1 < cand.0 {
        (ranges, Some(ErrorKind::InvalidRange(r.0, add)))
    } else {
        // the last-range rewrite spelled as take-prefix + push (the
        // value equals Seq::update(len-1, cand); the prefix form is
        // the compute-reducible shape)
        (ranges.subrange(0, ranges.len() - 1).push(cand), None)
    }
}

/// The class-content loop (glob.rs:1014-1065), one recursion per char:
/// the ']' first-then-break arm, the '-' trichotomy (first: literal
/// dash; in_range: extend the last range with '-'; else: the
/// pending-range latch, no push -- the ranges stay as they are), and
/// the literal/range general arm. The exit emissions: the closed class
/// token (with the trailing-'-' literal fold of glob.rs:1066-1070) or
/// the unclosed decision (rollback + latch + Literal('['), or the
/// UnclosedClass error).
pub open spec fn spec_class_loop(
    st: SState,
    saved_pos: int,
    negated: bool,
    first: bool,
    in_range: bool,
    ranges: Seq<(char, char)>,
) -> (SState, Option<ErrorKind>)
    decreases st.chars.len() - st.pos,
{
    let b = spec_bump(st);
    if b.1 is None {
        // glob.rs:1015-1026: the unclosed decision
        if st.opts.allow_unclosed_class {
            // rollback: cursor restored to the class entry, the latch
            // set, the Literal('[') push (glob.rs:1017-1022)
            let st_r = SState {
                chars: st.chars,
                stack: st.stack,
                brs: st.brs,
                pos: saved_pos,
                unclosed: true,
                opts: st.opts,
            };
            spec_push_token(st_r, TokenS::Lit('['))
        } else {
            (st, Some(ErrorKind::UnclosedClass))
        }
    } else {
        let c = b.1.get_Some_0();
        let st1 = b.0;
        if c == ']' {
            if first {
                spec_class_loop(st1, saved_pos, negated, false, in_range, ranges.push((']', ']')))
            } else {
                // the break: the class token emission; the trailing
                // '-' literal fold (glob.rs:1066-1070)
                let rs = if in_range {
                    ranges.push(('-', '-'))
                } else {
                    ranges
                };
                spec_push_token(st1, TokenS::Cls { negated, ranges: rs })
            }
        } else if c == '-' {
            if first {
                spec_class_loop(st1, saved_pos, negated, false, in_range, ranges.push(('-', '-')))
            } else if in_range {
                let up = spec_add_to_last(st1, ranges, '-');
                if up.1 is None {
                    spec_class_loop(st1, saved_pos, negated, false, false, up.0)
                } else {
                    (st1, up.1)
                }
            } else {
                spec_class_loop(st1, saved_pos, negated, false, true, ranges)
            }
        } else {
            if in_range {
                let up = spec_add_to_last(st1, ranges, c);
                if up.1 is None {
                    spec_class_loop(st1, saved_pos, negated, false, false, up.0)
                } else {
                    (st1, up.1)
                }
            } else {
                spec_class_loop(st1, saved_pos, negated, false, false, ranges.push((c, c)))
            }
        }
    }
}

/// parse_class entry (glob.rs:982-1011): the save / the negation peek
/// ('!' or '^'; glob.rs:1004-1011) / the content loop.
pub open spec fn spec_parse_class(st: SState) -> (SState, Option<ErrorKind>)
    decreases st.chars.len() - st.pos,
{
    let saved_pos = st.pos;
    let pk = spec_peek(st);
    let negated = pk is Some && (pk.get_Some_0() == '!' || pk.get_Some_0() == '^');
    let st1 = if negated {
        spec_bump(st).0
    } else {
        st
    };
    spec_class_loop(st1, saved_pos, negated, true, false, Seq::empty())
}

// -- parse_star (glob.rs:921-980) --

/// The ZeroOrMore x2 helper (glob.rs:930-931 / 943-944 / 959-960).
pub open spec fn spec_push_tokens2(st: SState, tok: TokenS) -> (SState, Option<ErrorKind>) {
    let p = spec_push_token(st, tok);
    if p.1 is None {
        spec_push_token(p.0, tok)
    } else {
        p
    }
}

/// parse_star (glob.rs:921-980). The lattice, in upstream order: the
/// single-'*' head; the '*' double-bump; the have_tokens == false head
/// (RecursivePrefix + the separator consume); the prev-separator /
/// alternate-context gate (ZeroOrMore x2); the suffix decision; the
/// pop/rewrite tail. The prev char (the char before the first '*') is
/// what decides the families -- pinned row-by-row against
/// oracle-run.txt:44-51,63-75 ("a**" -> Zom x2; "a/**/b" -> RecZ;
/// "/a**" -> Zom x2; "a/**/**" -> RecS).
pub open spec fn spec_parse_star(st: SState) -> (SState, Option<ErrorKind>)
    decreases st.chars.len() - st.pos,
{
    let prev = spec_prev(st);
    // glob.rs:923-926: the single '*'
    let pk0 = spec_peek(st);
    if !(pk0 is Some && pk0.get_Some_0() == '*') {
        spec_push_token(st, TokenS::Zom)
    } else {
        // glob.rs:927: the second '*' is consumed (the peek witnessed it)
        let st1 = spec_bump(st).0;
        // glob.rs:928-937: the have_tokens == false head
        let have = spec_have_tokens(st1);
        if have is Err {
            (st1, Some(have.get_Err_0()))
        } else if !have.get_Ok_0() {
            let pk1 = spec_peek(st1);
            // glob.rs:929: !peek.map_or(true, is_separator) -- Some
            // and NOT a separator
            if pk1 is Some && !sep_u(pk1.get_Some_0()) {
                spec_push_tokens2(st1, TokenS::Zom)
            } else {
                let p = spec_push_token(st1, TokenS::RecP);
                if p.1 is None {
                    // glob.rs:934: bump the witnessed separator (the
                    // None arm leaves pos at the end)
                    (spec_bump(p.0).0, None)
                } else {
                    p
                }
            }
        } else {
            // glob.rs:939-947: prev not a separator and no alternate
            // context: ZeroOrMore x2
            let prev_sep = prev is Some && sep_u(prev.get_Some_0());
            if !prev_sep
                && (st1.brs.len() <= 1 || (prev != Some(',') && prev != Some('{')))
            {
                spec_push_tokens2(st1, TokenS::Zom)
            } else {
                spec_star_tail(st1)
            }
        }
    }
}

/// The suffix decision + the pop/rewrite tail (glob.rs:948-979):
///   let is_suffix = match self.peek() {
///       None => true,
///       Some(',') | Some('}') if self.branches.len() >= 2 => true,
///       Some(c) if is_separator(c) => { bump; false }
///       _ => { Zom x2; return }
///   };
///   match self.pop_token()? {
///       RecursivePrefix => push RecursivePrefix,
///       RecursiveSuffix => push RecursiveSuffix,
///       _ => push (is_suffix ? RecursiveSuffix : RecursiveZeroOrMore),
///   }
pub open spec fn spec_star_tail(st: SState) -> (SState, Option<ErrorKind>) {
    let pk = spec_peek(st);
    if pk is None {
        // glob.rs:949-952: the end-of-pattern suffix
        spec_star_rewrite(st, true)
    } else if (pk.get_Some_0() == ',' || pk.get_Some_0() == '}') && st.brs.len() >= 2 {
        // glob.rs:953: the alternate-close suffix
        spec_star_rewrite(st, true)
    } else if sep_u(pk.get_Some_0()) {
        // glob.rs:954-957: consume the witnessed separator, not a suffix
        let st2 = spec_bump(st).0;
        let popped = spec_pop_token(st2);
        spec_star_rewrite2(st2, false, popped.1)
    } else {
        spec_push_tokens2(st, TokenS::Zom)
    }
}

/// glob.rs:964-979 (the non-consuming is_suffix arms).
pub open spec fn spec_star_rewrite(st: SState, is_suffix: bool) -> (SState, Option<ErrorKind>) {
    let popped = spec_pop_token(st);
    spec_star_rewrite2(st, is_suffix, popped.1)
}

/// The pop/rewrite lattice: the popped token's own family is preserved
/// (RecursivePrefix -> RecursivePrefix, RecursiveSuffix ->
/// RecursiveSuffix); the general arm rewrites by the suffix flag.
pub open spec fn spec_star_rewrite2(
    st: SState,
    is_suffix: bool,
    old: TokenS,
) -> (SState, Option<ErrorKind>) {
    if old is RecP {
        spec_push_token(st, TokenS::RecP)
    } else if old is RecS {
        spec_push_token(st, TokenS::RecS)
    } else if is_suffix {
        spec_push_token(st, TokenS::RecS)
    } else {
        spec_push_token(st, TokenS::RecZ)
    }
}

// -- the main loop (glob.rs:843-857) + the build entry (591-631) --

/// Origin Rust (glob.rs:843-857):
///     fn parse(&mut self) -> Result<(), Error> {
///         while let Some(c) = self.bump() {
///             match c {
///                 '?' => self.push_token(Token::Any)?,
///                 '*' => self.parse_star()?,
///                 '[' if !self.found_unclosed_class => self.parse_class()?,
///                 '{' => self.push_alternate()?,
///                 '}' => self.pop_alternate()?,
///                 ',' => self.parse_comma()?,
///                 '\\' => self.parse_backslash()?,
///                 c => self.push_token(Token::Literal(c))?,
///             }
///         }
///         Ok(())
///     }
pub open spec fn spec_parse_loop(st: SState, windows: bool, budget: int) -> (SState, Option<ErrorKind>)
    decreases budget,
{
    // The budget carries the termination argument (every loop pass
    // consumes at least one dispatched char, so budget == chars.len()
    // suffices; the KAT entry passes 2*len + 16 to leave slack for the
    // rollback/steps lattice). The budget == 0 arm below is therefore
    // never taken on the ground states the model is folded on.
    if budget <= 0 {
        (st, None)
    } else if st.pos >= st.chars.len() {
        (st, None)
    } else {
        let b = spec_bump(st);
        let c = b.1.get_Some_0();
        let st1 = b.0;
        // the one-iteration arm state (the upstream match arms in
        // order); the continuation below re-enters the loop
        let arm: (SState, Option<ErrorKind>) = if c == '?' {
            spec_push_token(st1, TokenS::Any)
        } else if c == '*' {
            spec_parse_star(st1)
        } else if c == '[' && !st1.unclosed {
            spec_parse_class(st1)
        } else if c == '[' {
            // '[' with the latch set: upstream's guard falls through to
            // the default literal arm (the allow_unclosed_class
            // rollback re-dispatch; oracle-run.txt:78,80)
            spec_push_token(st1, TokenS::Lit('['))
        } else if c == '{' {
            (spec_push_alternate(st1), None)
        } else if c == '}' {
            spec_pop_alternate(st1)
        } else if c == ',' {
            spec_parse_comma(st1)
        } else if c == '\\' {
            spec_parse_backslash(st1, windows)
        } else {
            spec_push_token(st1, TokenS::Lit(c))
        };
        if arm.1 is Some {
            arm
        } else {
            // the while-let continuation: the run continues from the
            // arm state (pos strictly advanced past the dispatched
            // char -- every arm leaves pos >= st.pos + 1)
            spec_parse_loop(arm.0, windows, budget - 1)
        }
    }
}

/// The build entry value model (glob.rs:600-631, the GL2 slice): the
/// parser init (glob.rs:601-610: branches = vec![Tokens::default()],
/// stack empty, cursor 0), the parse run, then the branch-count
/// epilogue -- len > 1 is UnclosedAlternates (glob.rs:617-621), len ==
/// 1 the popped token list. The len == 0 arm is upstream's
/// unreachable!() (glob.rs:613-616: "If we end up here, then there
/// *must* be a bug in the parser somewhere") -- kept as a column with
/// the UnclosedAlternates filler; the machine's own drain lattice
/// (windows start at stack entries >= 1) never reaches it.
pub open spec fn spec_parse_glob(chars: Seq<char>, opts: GlobOptions, windows: bool) -> Result<Seq<TokenS>, ErrorKind> {
    let st0 = SState {
        chars,
        stack: Seq::empty(),
        brs: Seq::empty().push(Seq::empty()),
        pos: 0,
        unclosed: false,
        opts,
    };
    let run = spec_parse_loop(st0, windows, (2 * chars.len() + 16) as int);
    if run.1 is Some {
        Err(run.1.get_Some_0())
    } else if run.0.brs.len() == 0 {
        // unreachable per glob.rs:613-616 (dead-branch filler)
        Err(ErrorKind::UnclosedAlternates)
    } else if run.0.brs.len() > 1 {
        Err(ErrorKind::UnclosedAlternates)
    } else {
        Ok(run.0.brs.index(0))
    }
}

// ===========================================================================
// THE EXEC MACHINE (glob.rs:811-1083, structural twin; the value oracle
// is the spec machine above -- the full exec==spec weave is the
// registered seam, notes.md W2).
//
// Safety obligations verified: no panic sites (the upstream assert!/
// unwrap() family re-derived as guards or invariants), cursor bounds,
// Vec index guards, usize arithmetic bounds; the machine carries its
// structural domain invariants (branches >= 1, stack entries in
// [1, branches.len()], the latch option-gated, prev/cur sync).
// ===========================================================================

/// The parser state (glob.rs:811-836); the chars/prev/cur iterator
/// triple becomes the pos cursor + the literal prev/cur fields (kept
/// in sync with spec_prev/spec_cur by the bump contract).
pub struct Parser {
    /// The glob to parse.
    pub glob: Vec<char>,
    /// Marks the index in `stack` where the alternation started.
    pub alternates_stack: Vec<usize>,
    /// The set of active alternation branches being parsed. Tokens are
    /// added to the end of the last one.
    pub branches: Vec<Vec<Token>>,
    /// The cursor into `glob` (the Peekable position).
    pub pos: usize,
    /// The previous character seen.
    pub prev: Option<char>,
    /// The current character.
    pub cur: Option<char>,
    /// Whether we failed to find a closing `]` for a character class.
    /// This can only be true when `GlobOptions::allow_unclosed_class`
    /// is enabled. When enabled, it is impossible to ever parse another
    /// character class with this glob. That's because classes cannot
    /// be nested *and* the only way this happens is when there is
    /// never a `]`.
    /// We track this state so that we don't end up spending quadratic
    /// time trying to parse something like `[[[[[[[[[[[[[[[[[[[[[[[...`.
    /// (glob.rs:825-833, verbatim)
    pub found_unclosed_class: bool,
    /// Glob options, which may influence parsing.
    pub opts: GlobOptions,
}

/// The machine domain invariant (the safety column): the
/// representability fence, cursor bounds, the branch/stack domain, and
/// the latch gate.
pub open spec fn p_dom(p: &Parser) -> bool {
    &&& p.glob.len() < 1073741824
    &&& p.pos <= p.glob.len()
    &&& p.branches.len() >= 1
    // every branch beyond the initial one consumes at least one
    // dispatched char ('{' or an in-group ','), so the branch count
    // never exceeds pos + 1
    &&& p.branches.len() <= p.pos + 1
    &&& forall|j: int| 0 <= j < p.alternates_stack.len() ==>
        1 <= p.alternates_stack[j] as int
    // the alternate-stack strict lattice (upstream's tacit domain:
    // entries are branch counts at push time, strictly increasing,
    // and the top always sits below the current branch count -- the
    // lattice behind `assert!(start <= self.branches.len())`,
    // glob.rs:869. NOTE: the stack-vs-branch LENGTH ratio clause is
    // deliberately absent -- it is a cardinality column the SMT
    // does not close from distinctness, and nothing in the machine
    // consumes it.)
    &&& forall|j: int, k: int| 0 <= j < k < p.alternates_stack.len() ==>
        p.alternates_stack[j] < p.alternates_stack[k]
    &&& p.alternates_stack.len() > 0
        ==> (p.alternates_stack[p.alternates_stack.len() - 1] as int)
            < (p.branches.len() as int)
    &&& p.found_unclosed_class ==> p.opts.allow_unclosed_class
    // NOTE: the deeper alternate-stack domain (entries strictly
    // increasing, top < branches.len() -- the lattice behind
    // upstream's `assert!(start <= self.branches.len())` at
    // glob.rs:869) is a cardinality-carrying column the SMT will not
    // close automatically; it feeds only the drain-window's value
    // delta, whose formal carrier is the spec machine's
    // spec_pop_alternate. The surviving stack clause below is the
    // cheap positivity fact (entries are branch counts >= 1) that the
    // drain cascade's landing guard rides on.
}

/// NOTE (the dropped sync column): an earlier draft carried a
/// p_prevcur invariant tying the exec prev/cur fields to the pos-
/// derived model values. It fails exactly at the exhaustion states
/// (upstream's `bump` at the pattern end still re-bases prev := cur
/// while cur := None, a state the pos-only derivation cannot name);
/// the exec twin now keeps upstream's literal fields and the spec
/// model derives prev/cur from pos, with the seam recorded in
/// notes.md W2 (the divergence state is never observable in the
/// parse products -- the exhaustion readers, parse_backslash and the
/// class unclosed decision, consult the state only to return their
/// errors/the rollback, both of which the spec models directly).

impl Parser {
    /// The GlobBuilder::build parser init (glob.rs:601-610):
    ///     let mut p = Parser {
    ///         glob: &self.glob,
    ///         alternates_stack: Vec::new(),
    ///         branches: vec![Tokens::default()],
    ///         chars: self.glob.chars().peekable(),
    ///         prev: None,
    ///         cur: None,
    ///         found_unclosed_class: false,
    ///         opts: &self.opts,
    ///     };
    pub fn new(glob: Vec<char>, opts: GlobOptions) -> (p: Parser)
        requires
            glob.len() < 1073741824,
        ensures
            p_dom(&p),
            p.branches@.len() == 1,
            p.branches@.index(0)@.len() == 0,
            p.alternates_stack@.len() == 0,
            p.pos == 0,
            p.found_unclosed_class == false,
            p.glob@ == glob@,
            p.opts == opts,
    {
        let mut p = Parser {
            glob,
            alternates_stack: Vec::new(),
            branches: Vec::new(),
            pos: 0,
            prev: None,
            cur: None,
            found_unclosed_class: false,
            opts,
        };
        p.branches.push(Vec::new());
        proof {
            assert(p_dom(&p));
        }
        p
    }

    // -------------------------------------------------------------------
    // bump / peek (glob.rs:1074-1082):
    //     fn bump(&mut self) -> Option<char> {
    //         self.prev = self.cur;
    //         self.cur = self.chars.next();
    //         self.cur
    //     }
    //     fn peek(&mut self) -> Option<char> {
    //         self.chars.peek().copied()
    //     }
    // -------------------------------------------------------------------

    fn bump(&mut self) -> (r: Option<char>)
        requires
            p_dom(&self),
        ensures
            p_dom(&*final(self)),
            final(self).glob@ == old(self).glob@,
            final(self).branches@ == old(self).branches@,
            final(self).alternates_stack@ == old(self).alternates_stack@,
            final(self).found_unclosed_class == old(self).found_unclosed_class,
            final(self).opts == old(self).opts,
            final(self).pos as int >= old(self).pos as int,
            final(self).pos as int <= old(self).pos as int + 1,
            final(self).pos <= final(self).glob.len(),
            old(self).pos < old(self).glob.len() ==> {
                &&& r is Some
                &&& r.get_Some_0() == old(self).glob@[old(self).pos as int]
                &&& final(self).pos == old(self).pos + 1
                &&& final(self).prev == old(self).cur
                &&& final(self).cur == Some(old(self).glob@[old(self).pos as int])
            },
            old(self).pos >= old(self).glob.len() ==> {
                &&& r is None
                &&& final(self).pos == old(self).pos
                &&& final(self).cur is None
                &&& final(self).prev == old(self).cur
            },
    {
        self.prev = self.cur;
        if self.pos < self.glob.len() {
            let c = self.glob[self.pos];
            self.cur = Some(c);
            self.pos += 1;
            Some(c)
        } else {
            self.cur = None;
            None
        }
    }

    fn peek(&self) -> (r: Option<char>)
        requires
            p_dom(&self),
        ensures
            r is Some ==> r.get_Some_0() == self.glob@[self.pos as int],
            r is Some ==> self.pos < self.glob.len(),
            r is None ==> self.pos == self.glob.len(),
    {
        if self.pos < self.glob.len() {
            Some(self.glob[self.pos])
        } else {
            None
        }
    }

    /// The error constructor (glob.rs:839-841).
    fn error(&self, kind: ErrorKind) -> (e: GlobError)
        ensures
            e.kind == kind,
    {
        GlobError { kind }
    }

    // -------------------------------------------------------------------
    // push_token (glob.rs:875-880); pop_token (glob.rs:882-887);
    // have_tokens (glob.rs:889-894). The pop's `.unwrap()` rides the
    // non-empty precondition (the callers arrive with have_tokens ==
    // true; pushes only grow the branch).
    // -------------------------------------------------------------------

    fn push_token(&mut self, tok: Token) -> (r: Result<(), GlobError>)
        requires
            p_dom(&self),
        ensures
            p_dom(&*final(self)),
            final(self).prev == old(self).prev,
            final(self).cur == old(self).cur,
            final(self).glob@ == old(self).glob@,
            final(self).opts == old(self).opts,
            final(self).pos == old(self).pos,
            final(self).found_unclosed_class == old(self).found_unclosed_class,
            final(self).alternates_stack@ == old(self).alternates_stack@,
            final(self).branches@.len() == old(self).branches@.len(),
            old(self).branches@.len() == 0 ==> {
                &&& r is Err
                &&& r.get_Err_0().kind matches ErrorKind::UnopenedAlternates
                &&& final(self).branches@ == old(self).branches@
            },
            old(self).branches@.len() > 0 ==> {
                &&& r is Ok
                &&& r is Ok
                &&& final(self).branches@.len() > 0
                &&& final(self).branches@.index(final(self).branches@.len() - 1)@.len()
                    == old(self).branches@.index(old(self).branches@.len() - 1)@.len() + 1
                &&& final(self).branches@.len() > 0
            },
    {
        if self.branches.len() > 0 {
            let n = self.branches.len();
            self.branches[n - 1].push(tok);
            Ok(())
        } else {
            Err(self.error(ErrorKind::UnopenedAlternates))
        }
    }

    fn pop_token(&mut self) -> (r: Result<Token, GlobError>)
        requires
            p_dom(&self),
            old(self).branches@.len() > 0,
            old(self).branches@.index(old(self).branches@.len() - 1)@.len() > 0,
        ensures
            p_dom(&*final(self)),
            final(self).prev == old(self).prev,
            final(self).cur == old(self).cur,
            final(self).glob@ == old(self).glob@,
            final(self).opts == old(self).opts,
            final(self).pos == old(self).pos,
            final(self).found_unclosed_class == old(self).found_unclosed_class,
            final(self).alternates_stack@ == old(self).alternates_stack@,
            final(self).branches@.len() == old(self).branches@.len(),
            final(self).branches@.len() > 0,
            final(self).branches@.index(final(self).branches@.len() - 1)@.len()
                == old(self).branches@.index(old(self).branches@.len() - 1)@.len() - 1,
            final(self).pos <= final(self).glob.len(),
            r is Ok,
            r.get_Ok_0()
                == old(self).branches@.index(old(self).branches@.len() - 1)@.index(
                    old(self).branches@.index(old(self).branches@.len() - 1)@.len() - 1,
                ),
    {
        let n = self.branches.len();
        // upstream: `Ok(pat.pop().unwrap())` -- the pop moves the last
        // token out (the unwrap's guard is the non-empty precondition)
        match self.branches[n - 1].pop() {
            Some(tok) => Ok(tok),
            None => Err(self.error(ErrorKind::UnopenedAlternates)),
        }
    }

    fn have_tokens(&self) -> (r: Result<bool, GlobError>)
        requires
            p_dom(&self),
        ensures
            self.branches@.len() == 0 ==> {
                &&& r is Err
                &&& r.get_Err_0().kind matches ErrorKind::UnopenedAlternates
            },
            self.branches@.len() > 0 ==> {
                &&& r is Ok
                &&& r is Ok
                &&& r.get_Ok_0() == (self.branches@.index(self.branches@.len() - 1)@.len() > 0)
            },
    {
        if self.branches.len() == 0 {
            Err(self.error(ErrorKind::UnopenedAlternates))
        } else {
            Ok(self.branches[self.branches.len() - 1].len() > 0)
        }
    }

    // -------------------------------------------------------------------
    // push_alternate (glob.rs:859-863) / pop_alternate (glob.rs:865-873)
    // -------------------------------------------------------------------

    fn push_alternate(&mut self) -> (r: Result<(), GlobError>)
        requires
            p_dom(&self),
            // the dispatched '{' already advanced the cursor, so the
            // new branch (old count + 1) stays within pos + 1
            old(self).branches.len() <= old(self).pos,
        ensures
            p_dom(&*final(self)),
            final(self).prev == old(self).prev,
            final(self).cur == old(self).cur,
            final(self).glob@ == old(self).glob@,
            final(self).opts == old(self).opts,
            final(self).pos == old(self).pos,
            final(self).found_unclosed_class == old(self).found_unclosed_class,
            final(self).branches@.len() == old(self).branches@.len() + 1,
            final(self).branches@.index(final(self).branches@.len() - 1)@.len() == 0,
            final(self).alternates_stack@.len() == old(self).alternates_stack@.len() + 1,
            final(self).alternates_stack@.index(final(self).alternates_stack@.len() - 1)
                == old(self).branches@.len(),
            r is Ok,
    {
        self.alternates_stack.push(self.branches.len());
        self.branches.push(Vec::new());
        proof {
            // the strict lattice after the entry append: the new top
            // (the old branch count) sits above every earlier entry
            // (the old top was < the old branch count), and below the
            // new branch count (old + 1)
            let n = self.alternates_stack.len();
            let nb = self.branches.len();
            assert(nb as int == (old(self).branches.len() as int) + 1);
            assert(self.alternates_stack@.len() == (old(self).alternates_stack@.len() as int) + 1);
            assert forall|j: int, k: int| 0 <= j < k < (n as int) implies
                (self.alternates_stack[j] as int) < (self.alternates_stack[k] as int)
            by {
                if k == (n as int) - 1 {
                    // the new entry is the old branch count; every
                    // earlier entry sat at or below the old top, which
                    // was strictly below the old branch count
                    assert((self.alternates_stack[k] as int) == (old(self).branches.len() as int));
                    if old(self).alternates_stack.len() > 0 {
                        let ol = old(self).alternates_stack.len() - 1;
                        assert((old(self).alternates_stack[ol] as int)
                            < (old(self).branches.len() as int));
                        if j < (ol as int) {
                            assert((old(self).alternates_stack[j] as int)
                                < (old(self).alternates_stack[ol] as int));
                        } else {
                            assert(j as int == ol);
                        }
                    }
                } else {
                    assert(self.alternates_stack[j] == old(self).alternates_stack[j]);
                    assert(self.alternates_stack[k] == old(self).alternates_stack[k]);
                }
            }
            if n > 0 {
                let lst = self.alternates_stack[n - 1];
                assert((lst as int) < (nb as int)) by {
                    assert((lst as int) == (old(self).branches.len() as int));
                }
                assert(1 <= (lst as int)) by {
                    assert((old(self).branches.len() as int) >= 1);
                }
            }
            assert(self.pos <= self.glob.len());
            assert(self.branches.len() >= 1);
            assert(self.branches.len() == nb);
            assert(self.branches.len() == old(self).branches.len() + 1);
            assert(self.branches.len() <= self.pos + 1);
            assert(self.found_unclosed_class ==> self.opts.allow_unclosed_class);
        }
        Ok(())
    }

    /// pop_alternate. Upstream's `assert!(start <= self.branches.len())`
    /// (glob.rs:869) rides the machine domain (the stack-entry lattice:
    /// entries are branch counts pushed by push_alternate and the pops
    /// drain above them); the exec drain is a tail-pop cascade
    /// (value-equal to upstream's drain(start..).collect(): the
    /// elements come out reversed and are re-reversed by the second
    /// cascade).
    fn pop_alternate(&mut self) -> (r: Result<(), GlobError>)
        requires
            p_dom(&self),
        ensures
            p_dom(&*final(self)),
            final(self).prev == old(self).prev,
            final(self).cur == old(self).cur,
            final(self).glob@ == old(self).glob@,
            final(self).opts == old(self).opts,
            final(self).pos == old(self).pos,
            final(self).found_unclosed_class == old(self).found_unclosed_class,
            old(self).alternates_stack@.len() == 0 ==> {
                &&& r is Err
                &&& r is Err
                &&& r.get_Err_0().kind matches ErrorKind::UnopenedAlternates
                &&& final(self).branches@ == old(self).branches@
                &&& final(self).alternates_stack@ == old(self).alternates_stack@
            },
            old(self).alternates_stack@.len() > 0 ==> {
                &&& final(self).alternates_stack@.len()
                    == old(self).alternates_stack@.len() - 1
                &&& final(self).alternates_stack@.len() >= 0
                &&& (r is Ok ==> final(self).branches@.len() >= 1)
                &&& (r is Ok
                    ==> final(self).branches@.len() <= old(self).branches@.len())
                &&& (r is Err ==> r.get_Err_0().kind matches ErrorKind::UnopenedAlternates)
            },
    {
        let top = self.alternates_stack.len();
        if top == 0 {
            return Err(self.error(ErrorKind::UnopenedAlternates));
        }
        let start = self.alternates_stack[top - 1];
        proof {
            // p_dom's stack positivity + strict top: the top entry
            // (== start) satisfies 1 <= start < branches.len()
            assert(1 <= start);
            assert((start as int) < (self.branches.len() as int));
        }
        match self.alternates_stack.pop() {
            Some(_) => {},
            None => {
                assert(false);
            },
        }
        proof {
            // the post-pop stack: the prefix facts survive the pop; a
            // nonempty remainder has its own top strictly below start
            // (the pre-pop adjacency + the popped top == start)
            let n_after = self.alternates_stack.len();
            assert(n_after as int == (old(self).alternates_stack.len() as int) - 1);
            assert forall|j: int, k: int|
                0 <= j < k < (n_after as int) implies
                    (self.alternates_stack[j] as int) < (self.alternates_stack[k] as int)
            by {
                assert(self.alternates_stack[j] == old(self).alternates_stack[j]);
                assert(self.alternates_stack[k] == old(self).alternates_stack[k]);
            }
            assert forall|j: int| 0 <= j < n_after implies
                (self.alternates_stack[j] as int) >= 1
            by {
                assert(self.alternates_stack[j] == old(self).alternates_stack[j]);
            }
            if self.alternates_stack.len() > 0 {
                let lt = self.alternates_stack.len() - 1;
                assert((self.alternates_stack[lt] as int) < (start as int)) by {
                    assert(self.alternates_stack[lt] == old(self).alternates_stack[lt]);
                    assert((old(self).alternates_stack[lt] as int)
                        < (old(self).alternates_stack[old(self).alternates_stack.len() - 1] as int));
                }
            }
        }
        // the drain cascade: tail-pops collect the window reversed
        let mut rev: Vec<Vec<Token>> = Vec::new();
        while self.branches.len() > start
            invariant
                p_dom(&self),
                self.glob@ == old(self).glob@,
                self.opts == old(self).opts,
                self.pos == old(self).pos,
                self.prev == old(self).prev,
                self.cur == old(self).cur,
                self.found_unclosed_class == old(self).found_unclosed_class,
                // the post-pop stack: one entry (the window start)
                // gone, the rest untouched
                self.alternates_stack@.len()
                    == old(self).alternates_stack@.len() - 1,
                start <= self.branches.len(),
                start >= 1,
                // the frozen post-pop stack facts (see the proof block
                // above): a nonempty remainder tops strictly below start
                self.alternates_stack.len() == 0
                    || (self.alternates_stack[self.alternates_stack.len() - 1] as int)
                        < (start as int),
                rev.len() == old(self).branches.len() - self.branches.len(),
            decreases self.branches.len() - start,
        {
            match self.branches.pop() {
                Some(br) => rev.push(br),
                None => {
                    assert(false);
                },
            }
        }
        // the re-reverse cascade: the window in upstream order
        let mut window: Vec<Vec<Token>> = Vec::new();
        while rev.len() > 0
            invariant
                p_dom(&self),
                self.glob@ == old(self).glob@,
                self.opts == old(self).opts,
                self.pos == old(self).pos,
                self.prev == old(self).prev,
                self.cur == old(self).cur,
                self.found_unclosed_class == old(self).found_unclosed_class,
                self.alternates_stack@.len()
                    == old(self).alternates_stack@.len() - 1,
                start <= self.branches.len(),
                start >= 1,
                self.branches.len() == start,
                self.alternates_stack.len() == 0
                    || (self.alternates_stack[self.alternates_stack.len() - 1] as int)
                        < (start as int),
                window.len() + rev.len()
                    == old(self).branches.len() - self.branches.len(),
            decreases rev.len(),
        {
            match rev.pop() {
                Some(br) => window.push(br),
                None => {
                    assert(false);
                },
            }
        }
        let alts = Token::Alternates(window);
        if self.branches.len() == 0 {
            // the whole-list window (start == 0): unreachable through
            // the machine's own lattice (stack entries >= 1); the
            // error column mirrors push_token's
            return Err(self.error(ErrorKind::UnopenedAlternates));
        }
        self.push_token(alts)
    }

    // -------------------------------------------------------------------
    // parse_comma (glob.rs:896-905):
    //     // If we aren't inside a group alternation, then don't
    //     // treat commas specially. Otherwise, we need to start
    //     // a new alternate branch.
    //     if self.alternates_stack.is_empty() {
    //         self.push_token(Token::Literal(','))
    //     } else {
    //         Ok(self.branches.push(Tokens::default()))
    //     }
    // -------------------------------------------------------------------

    fn parse_comma(&mut self) -> (r: Result<(), GlobError>)
        requires
            p_dom(&self),
            // the dispatched ',' already advanced the cursor (the
            // in-group growth arm stays within pos + 1)
            old(self).branches.len() <= old(self).pos,
        ensures
            p_dom(&*final(self)),
            final(self).prev == old(self).prev,
            final(self).cur == old(self).cur,
            final(self).glob@ == old(self).glob@,
            final(self).opts == old(self).opts,
            final(self).pos == old(self).pos,
            final(self).prev == old(self).prev,
            final(self).cur == old(self).cur,
            final(self).found_unclosed_class == old(self).found_unclosed_class,
            final(self).alternates_stack@ == old(self).alternates_stack@,
            old(self).alternates_stack@.len() > 0 ==> {
                &&& r is Ok
                &&& final(self).branches@.len() == old(self).branches@.len() + 1
                &&& final(self).branches@.index(final(self).branches@.len() - 1)@.len() == 0
            },
            r is Err ==> r.get_Err_0().kind matches ErrorKind::UnopenedAlternates,
    {
        if self.alternates_stack.len() == 0 {
            // If we aren't inside a group alternation, then don't
            // treat commas specially. Otherwise, we need to start
            // a new alternate branch.
            let pr = self.push_token(Token::Literal(','));
            match pr {
                Err(e) => {
                    proof {
                        assert(self.alternates_stack@ == old(self).alternates_stack@);
                        assert(self.branches@.len() == old(self).branches@.len());
                    }
                    Err(e)
                },
                Ok(()) => {
                    proof {
                        assert(self.alternates_stack@ == old(self).alternates_stack@);
                        assert(self.branches@.len() == old(self).branches@.len());
                        assert(self.pos <= self.glob.len());
                        assert(self.branches.len() >= 1);
                        assert(self.branches.len() <= self.pos + 1);
                        assert(self.found_unclosed_class ==> self.opts.allow_unclosed_class);
                        assert(p_dom(&self));
                    }
                    Ok(())
                },
            }
        } else {
            self.branches.push(Vec::new());
            proof {
                // the stack untouched; the branch count grew by one, so
                // the strict-top clause widens
                assert(self.alternates_stack@ == old(self).alternates_stack@);
                assert(self.branches@.len() == old(self).branches@.len() + 1);
                let n = self.alternates_stack.len();
                assert forall|j: int|
                    0 <= j < (n as int) implies 1 <= (self.alternates_stack[j] as int)
                by {
                    assert(self.alternates_stack[j] == old(self).alternates_stack[j]);
                }
                assert forall|j: int, k: int|
                    0 <= j < k < (n as int) implies
                        (self.alternates_stack[j] as int) < (self.alternates_stack[k] as int)
                by {
                    assert(self.alternates_stack[j] == old(self).alternates_stack[j]);
                    assert(self.alternates_stack[k] == old(self).alternates_stack[k]);
                }
                if n > 0 {
                    let lst = self.alternates_stack[n - 1];
                    assert((lst as int) < (self.branches.len() as int)) by {
                        assert((lst as int) < (old(self).branches.len() as int));
                    }
                }
                assert(self.pos <= self.glob.len());
                assert(self.branches.len() >= 1);
                assert(self.branches.len() <= self.pos + 1);
                assert(self.found_unclosed_class ==> self.opts.allow_unclosed_class);
                assert(p_dom(&self));
            }
            Ok(())
        }
    }

    // -------------------------------------------------------------------
    // parse_backslash (glob.rs:907-919):
    //     if self.opts.backslash_escape {
    //         match self.bump() {
    //             None => Err(self.error(ErrorKind::DanglingEscape)),
    //             Some(c) => self.push_token(Token::Literal(c)),
    //         }
    //     } else if is_separator('\\') {
    //         // Normalize all patterns to use / as a separator.
    //         self.push_token(Token::Literal('/'))
    //     } else {
    //         self.push_token(Token::Literal('\\'))
    //     }
    // (the is_separator('\\') arm is oracle-parameterized; oracle-run.
    // txt:76-77 pins both readings of "a\b" under the unix set)
    // -------------------------------------------------------------------

    fn parse_backslash(&mut self, windows: bool) -> (r: Result<(), GlobError>)
        requires
            p_dom(&self),
        ensures
            p_dom(&*final(self)),
            final(self).glob@ == old(self).glob@,
            final(self).opts == old(self).opts,
            final(self).alternates_stack@ == old(self).alternates_stack@,
            final(self).found_unclosed_class == old(self).found_unclosed_class,
            r is Err ==> (r.get_Err_0().kind matches ErrorKind::DanglingEscape
                || r.get_Err_0().kind matches ErrorKind::UnopenedAlternates),
            final(self).pos as int >= old(self).pos as int,
            final(self).pos as int <= old(self).pos as int + 1,
    {
        if self.opts.backslash_escape {
            let b = self.bump();
            match b {
                Some(c) => self.push_token(Token::Literal(c)),
                None => Err(self.error(ErrorKind::DanglingEscape)),
            }
        } else if char_is_sep_exec(0x5c as char, windows) {
            // Normalize all patterns to use / as a separator.
            self.push_token(Token::Literal('/'))
        } else {
            self.push_token(Token::Literal('\\'))
        }
    }

    // -------------------------------------------------------------------
    // parse_star (glob.rs:921-980) -- the exec lattice, arms in upstream
    // order. The three embedded assert!s are re-derived guards:
    //   glob.rs:927  (bump == Some('*'))  -- the branch was gated on
    //               peek() == Some('*'), and the bump reads that char;
    //   glob.rs:934  (bump.map_or(true, is_separator)) -- the arm fired
    //               exactly on the None-or-separator peek;
    //   glob.rs:950/955 -- same identity for the suffix decision.
    // -------------------------------------------------------------------

    fn parse_star(&mut self, windows: bool) -> (r: Result<(), GlobError>)
        requires
            p_dom(&self),
            old(self).glob.len() > 0,
            old(self).pos > 0,
            old(self).pos <= old(self).glob.len(),
            old(self).glob@[old(self).pos as int - 1] == '*',
        ensures
            p_dom(&*final(self)),
            final(self).glob@ == old(self).glob@,
            final(self).opts == old(self).opts,
            final(self).pos as int >= old(self).pos as int,
            final(self).pos as int <= old(self).pos as int + 2,
            final(self).found_unclosed_class ==> final(self).opts.allow_unclosed_class,
            r is Err ==> is_parse_error(r.get_Err_0().kind),
        decreases self.glob.len() - self.pos,
    {
        let prev = self.prev;
        // glob.rs:923-926: the single '*'
        let pk0 = self.peek();
        let single_star: bool = match pk0 {
            Some(c) => c != '*',
            None => true,
        };
        if single_star {
            return self.push_token(Token::ZeroOrMore);
        }
        // glob.rs:927: the second '*' is consumed (the peek witnessed it)
        match self.bump() {
            Some(c) => {
                assert(c == '*');
            },
            None => {
                assert(false);
            },
        }
        // glob.rs:928-937: the have_tokens == false head
        let have = self.have_tokens();
        match have {
            Err(e) => return Err(e),
            Ok(have_some) => {
                if !have_some {
                    let pk1 = self.peek();
                    let plain_next: bool = match pk1 {
                        Some(c) => !char_is_sep_exec(c, windows),
                        None => false,
                    };
                    if plain_next {
                        let p1 = self.push_token(Token::ZeroOrMore);
                        match p1 {
                            Err(e) => return Err(e),
                            Ok(()) => {},
                        }
                        return self.push_token(Token::ZeroOrMore);
                    } else {
                        let p1 = self.push_token(Token::RecursivePrefix);
                        match p1 {
                            Err(e) => return Err(e),
                            Ok(()) => {},
                        }
                        // glob.rs:934: bump the witnessed separator (the
                        // None arm leaves pos at the end)
                        match self.bump() {
                            Some(c2) => {
                                assert(char_is_sep(c2, windows));
                            },
                            None => {},
                        }
                        return Ok(());
                    }
                }
            },
        }
        // glob.rs:939-947: the prev-separator / alternate-context gate
        let prev_sep: bool = match prev {
            Some(c) => char_is_sep_exec(c, windows),
            None => false,
        };
        if !prev_sep {
            if self.branches.len() <= 1 || (prev != Some(',') && prev != Some('{')) {
                let p1 = self.push_token(Token::ZeroOrMore);
                match p1 {
                    Err(e) => return Err(e),
                    Ok(()) => {},
                }
                return self.push_token(Token::ZeroOrMore);
            }
        }
        // glob.rs:948-963: the suffix decision
        let pk = self.peek();
        let at_end: bool = match pk {
            None => true,
            Some(_) => false,
        };
        let alt_close: bool = match pk {
            Some(c) => (c == ',' || c == '}') && self.branches.len() >= 2,
            None => false,
        };
        let sep_next: bool = match pk {
            Some(c) => !alt_close && char_is_sep_exec(c, windows),
            None => false,
        };
        let is_suffix: bool;
        if at_end {
            // glob.rs:950: assert!(self.bump().is_none()) -- at the
            // end position the bump returns None
            is_suffix = true;
        } else if alt_close {
            is_suffix = true;
        } else if sep_next {
            // glob.rs:955: the bump reads back the witnessed separator
            match self.bump() {
                Some(c3) => {
                    assert(char_is_sep(c3, windows));
                },
                None => {
                    assert(false);
                },
            }
            is_suffix = false;
        } else {
            let p1 = self.push_token(Token::ZeroOrMore);
            match p1 {
                Err(e) => return Err(e),
                Ok(()) => {},
            }
            return self.push_token(Token::ZeroOrMore);
        }
        // glob.rs:964-979: the pop/rewrite lattice (the pop rides the
        // have_tokens == true fact -- pushes only grow the branch)
        let popped = self.pop_token();
        match popped {
            Err(e) => return Err(e),
            Ok(tok) => {
                let chosen: Token = match tok {
                    Token::RecursivePrefix => Token::RecursivePrefix,
                    Token::RecursiveSuffix => Token::RecursiveSuffix,
                    _ => if is_suffix {
                        Token::RecursiveSuffix
                    } else {
                        Token::RecursiveZeroOrMore
                    },
                };
                self.push_token(chosen)
            },
        }
    }

    // -------------------------------------------------------------------
    // parse_class (glob.rs:982-1072) -- the exec lattice. The
    // last_mut().unwrap() pair (glob.rs:1041,1052) rides the
    // first/in_range latch invariant (every non-first iteration has
    // pushed at least one range); the negation assert (glob.rs:1007)
    // reads back the peeked char.
    // -------------------------------------------------------------------

    fn parse_class(&mut self) -> (r: Result<(), GlobError>)
        requires
            p_dom(&self),
            old(self).glob.len() > 0,
            old(self).pos > 0,
            old(self).pos <= old(self).glob.len(),
            old(self).glob@[old(self).pos as int - 1] == '[',
            // the '['-guarded dispatch arm (glob.rs:848) guarantees the
            // latch is clear on entry (the rollback lattice within this
            // method is the only setter, and it exits the class regime)
            old(self).found_unclosed_class == false,
        ensures
            p_dom(&*final(self)),
            final(self).glob@ == old(self).glob@,
            final(self).opts == old(self).opts,
            final(self).pos as int >= old(self).pos as int,
            final(self).pos as int <= old(self).glob.len(),
            final(self).found_unclosed_class ==> final(self).opts.allow_unclosed_class,
            r is Err ==> is_parse_error(r.get_Err_0().kind),
        decreases self.glob.len() - self.pos,
    {
        // Save parser state for potential rollback to literal '[' parsing.
        // (glob.rs:983-986)
        let saved_pos: usize = self.pos;
        proof {
            assert(saved_pos == old(self).pos);
        }
        let saved_prev = self.prev;
        let saved_cur = self.cur;

        let mut ranges: Vec<(char, char)> = Vec::new();
        // glob.rs:1004-1011: the negation peek ('!' or '^')
        let pk = self.peek();
        let negated: bool = match pk {
            Some(c) => c == '!' || c == '^',
            None => false,
        };
        let negated: bool = if negated {
            match self.bump() {
                Some(b) => {
                    // glob.rs:1007: assert!(bump == Some('!') ||
                    // bump == Some('^')) -- reads back the peek
                    assert(b == '!' || b == '^');
                },
                None => {
                    assert(false);
                },
            }
            true
        } else {
            false
        };
        let mut first = true;
        let mut in_range = false;
        // The class-content loop (glob.rs:1014-1065): terminates at the
        // closing ']' break, the exhaustion return (unclosed), or an
        // InvalidRange error return.
        let mut closed = false;
        while !closed
            invariant
                p_dom(&self),
                self.glob@ == old(self).glob@,
                self.opts == old(self).opts,
                self.alternates_stack@ == old(self).alternates_stack@,
                self.branches@.len() == old(self).branches@.len(),
                self.branches@.len() <= (saved_pos as int) + 1,
                saved_pos == old(self).pos,
                saved_pos <= self.pos,
                self.pos <= self.glob.len(),
                self.branches@.len() >= 1,
                forall|j: int| 0 <= j < self.alternates_stack.len() ==>
                    1 <= self.alternates_stack[j] as int,
                forall|j: int, k: int|
                    0 <= j < k < self.alternates_stack.len() ==>
                        self.alternates_stack[j] < self.alternates_stack[k],
                self.alternates_stack.len() > 0
                    ==> (self.alternates_stack[self.alternates_stack.len() - 1] as int)
                        < (self.branches.len() as int),
                self.found_unclosed_class ==> self.opts.allow_unclosed_class,
                // in_range only set when a range exists (glob.rs:1039-1041)
                in_range ==> ranges.len() > 0,
                // the latch arm only fires under the option, and only
                // together with the closed exit
                self.found_unclosed_class ==> closed,
                closed ==> self.pos == if self.found_unclosed_class {
                    saved_pos
                } else {
                    self.pos
                },
            decreases self.glob.len() - self.pos,
        {
            let c_opt = self.bump();
            let c = match c_opt {
                None => {
                    // glob.rs:1016-1025: the unclosed decision
                    if self.opts.allow_unclosed_class {
                        // rollback: cursor restored, latch set, literal '['
                        self.pos = saved_pos;
                        self.prev = saved_prev;
                        self.cur = saved_cur;
                        self.found_unclosed_class = true;
                        closed = true;
                        proof {
                            // the branch count bound survives the
                            // restore (pos is back at the class entry,
                            // and the count never moved)
                            assert(self.pos == saved_pos);
                            assert(self.branches.len() == old(self).branches.len());
                            assert(self.branches.len() <= saved_pos + 1);
                            assert(p_dom(&self));
                        }
                        let p1 = self.push_token(Token::Literal('['));
                        match p1 {
                            Err(e) => return Err(e),
                            Ok(()) => {},
                        }
                    } else {
                        proof {
                            // the p_dom conjuncts assembled from the
                            // loop invariants at this exit (the class
                            // regime never touches the stack or branch
                            // count)
                            assert(self.glob.len() < 1073741824);
                            assert(self.branches.len() <= self.pos + 1);
                            assert(p_dom(&self));
                            assert(self.pos <= self.glob.len());
                            assert(self.branches.len() >= 1);
                            assert(self.found_unclosed_class ==> self.opts.allow_unclosed_class);
                            assert(self.alternates_stack@.len() == old(self).alternates_stack@.len());
                            assert(self.branches@.len() == old(self).branches@.len());
                            assert forall|j: int|
                                0 <= j < self.alternates_stack.len() implies
                                    1 <= (self.alternates_stack[j] as int)
                            by {
                                assert(self.alternates_stack@ == old(self).alternates_stack@);
                                assert(self.alternates_stack[j] == old(self).alternates_stack[j]);
                            }
                            assert forall|j: int, k: int|
                                0 <= j < k < self.alternates_stack.len() implies
                                    (self.alternates_stack[j] as int)
                                        < (self.alternates_stack[k] as int)
                            by {
                                assert(self.alternates_stack@ == old(self).alternates_stack@);
                                assert(self.alternates_stack[j] == old(self).alternates_stack[j]);
                                assert(self.alternates_stack[k] == old(self).alternates_stack[k]);
                            }
                            let n = self.alternates_stack.len();
                            if n > 0 {
                                let lst = self.alternates_stack[n - 1];
                                assert((lst as int) < (self.branches.len() as int)) by {
                                    assert(self.branches.len() == old(self).branches.len());
                                }
                            }
                        }
                        return Err(self.error(ErrorKind::UnclosedClass));
                    }
                    // the unclosed arm ends the loop (closed latch
                    // set, or the error returned); the break skips the
                    // decreases check on the pos-restoring rollback
                    break;
                },
                Some(cx) => cx,
            };
                if c == ']' {
                    if first {
                        ranges.push((']', ']'));
                    } else {
                        closed = true;
                    }
                } else if c == '-' {
                    if first {
                        ranges.push(('-', '-'));
                    } else if in_range {
                        // glob.rs:1039-1043: extend the last range with
                        // '-' (add_to_last_range's order check inline:
                        // the InvalidRange(start, '-') error column)
                        let n = ranges.len();
                        let last = ranges[n - 1];
                        if '-' < last.0 {
                            return Err(GlobError::error(ErrorKind::InvalidRange(last.0, '-')));
                        }
                        ranges[n - 1] = (last.0, '-');
                        in_range = false;
                    } else {
                        // glob.rs:1045: assert!(!ranges.is_empty()) --
                        // every non-first iteration pushed a range
                        ranges.push(('-', '-'));
                        in_range = true;
                    }
                } else {
                    if in_range {
                        // glob.rs:1050-1057: extend the last range with
                        // c (the order check, InvalidRange(start, c))
                        let n = ranges.len();
                        let last = ranges[n - 1];
                        if c < last.0 {
                            return Err(GlobError::error(ErrorKind::InvalidRange(last.0, c)));
                        }
                        ranges[n - 1] = (last.0, c);
                    } else {
                        ranges.push((c, c));
                    }
                    in_range = false;
                }
                first = false;
        }
        // glob.rs:1066-1070: the trailing '-' literal (the class closed
        // with a pending range)
        if in_range && !self.found_unclosed_class {
            ranges.push(('-', '-'));
        }
        self.push_token(Token::Class { negated, ranges })
    }

    // -------------------------------------------------------------------
    // parse (the main loop, glob.rs:843-857).
    // -------------------------------------------------------------------

    pub fn parse(&mut self, windows: bool) -> (r: Result<(), GlobError>)
        requires
            p_dom(&self),
            old(self).pos == 0,
        ensures
            p_dom(&*final(self)),
            final(self).glob@ == old(self).glob@,
            final(self).opts == old(self).opts,
            final(self).pos <= final(self).glob.len(),
            final(self).branches@.len() >= 1,
            final(self).found_unclosed_class ==> final(self).opts.allow_unclosed_class,
            r is Ok ==> final(self).pos == final(self).glob.len(),
            r is Err ==> is_parse_error(r.get_Err_0().kind),
    {
        let mut guard: usize = 0;
        while self.pos < self.glob.len()
            invariant
                p_dom(&self),
                self.glob@ == old(self).glob@,
                self.opts == old(self).opts,
                self.pos <= self.glob.len(),
                self.branches@.len() >= 1,
                self.branches@.len() <= (self.pos as int) + 1,
                self.branches.len() <= self.pos + 1,
                guard <= self.pos,
                self.found_unclosed_class ==> self.opts.allow_unclosed_class,
            decreases self.glob.len() - self.pos,
        {
            let head_pos: usize = self.pos;
            let c_opt = self.bump();
            let c = match c_opt {
                // unreachable: the loop guard bounds pos < len
                None => {
                    assert(false);
                    return Ok(());
                },
                Some(cx) => cx,
            };
            proof {
                // the dispatch bump consumed exactly one char
                assert(self.pos as int == (head_pos as int) + 1);
                assert(self.glob@[(self.pos as int) - 1] == c);
            }
            let mut arm_err: Option<GlobError> = None;
            if c == '?' {
                match self.push_token(Token::Any) {
                    Err(e) => arm_err = Some(e),
                    Ok(()) => {},
                }
            } else if c == '*' {
                match self.parse_star(windows) {
                    Err(e) => arm_err = Some(e),
                    Ok(()) => {},
                }
            } else if c == '[' && !self.found_unclosed_class {
                match self.parse_class() {
                    Err(e) => arm_err = Some(e),
                    Ok(()) => {},
                }
            } else if c == '[' {
                // the latch set: the default literal arm
                match self.push_token(Token::Literal('[')) {
                    Err(e) => arm_err = Some(e),
                    Ok(()) => {},
                }
            } else if c == '{' {
                match self.push_alternate() {
                    Err(e) => arm_err = Some(e),
                    Ok(()) => {},
                }
            } else if c == '}' {
                match self.pop_alternate() {
                    Err(e) => arm_err = Some(e),
                    Ok(()) => {},
                }
            } else if c == ',' {
                match self.parse_comma() {
                    Err(e) => arm_err = Some(e),
                    Ok(()) => {},
                }
            } else if c == '\\' {
                match self.parse_backslash(windows) {
                    Err(e) => arm_err = Some(e),
                    Ok(()) => {},
                }
            } else {
                match self.push_token(Token::Literal(c)) {
                    Err(e) => arm_err = Some(e),
                    Ok(()) => {},
                }
            }
            match arm_err {
                Some(e) => return Err(e),
                None => {},
            }
            proof {
                assert(self.pos as int >= (head_pos as int) + 1);
            }
            guard += 1;
        }
        Ok(())
    }
}

// ===========================================================================
// GL3 -- THE REGEX-LOWERING FACE (glob.rs:694-809): to_regex_with /
// tokens_to_regex (the per-token emission table), the `**`-alone
// special case, char_to_escaped_literal / bytes_to_escaped_literal
// (the `\xNN` self-arm), and the regex_syntax::escape_into trusted
// face (regex-syntax 0.8.11 per the upstream Cargo.lock pin; the only
// regex-syntax surface globset's lowering consumes, and exclusively
// over single ASCII chars -- glob.rs:800's `b <= 0x7F` gate).
//
// Transcription decisions (GL3):
//  - String/str == Seq<char>/Vec<char> (the GL1 chars base; every
//    emission below is pure ASCII, sealed by the ascii_only assembly
//    theorem family).
//  - The lowering is stated twice like the parser layer: a value
//    machine over TokenS (spec_to_regex_with + family, the KAT
//    carrier) and a safety-verified exec twin over Token
//    (to_regex_with_exec + tokens_to_regex_exec, upstream shape with
//    a depth budget column on the alternates recursion -- verus
//    demands a terminating measure where upstream recurses freely;
//    the exec==spec value weave is the GL2 W2 seam, unchanged).
//  - The `\xNN` self-arm is transcribed as the two-lowercase-digit
//    hex emission (std's `write!(..,{:02x})` is a formatting oracle;
//    hex_digit's 16-way table is the verus spelling, and the
//    well-formedness of every emitted pair is a proved family).
// ===========================================================================

// ---------------------------------------------------------------------------
// The escape_into face (TRUSTED TRANSCRIPTION).
//
// Origin Rust (regex-syntax 0.8.11, src/lib.rs:213-219 + 261-279, the
// version pinned by upstream's Cargo.lock; regex-syntax is external to
// the transcribed tree, so this face is trusted-by-transcription --
// its faithfulness is cross-checked by the GL3 oracle arm, which runs
// the same two upstream functions verbatim against the upstream test
// suite's own expected regex strings):
//     pub fn escape_into(text: &str, buf: &mut String) {
//         buf.reserve(text.len());
//         for c in text.chars() {
//             if is_meta_character(c) {
//                 buf.push('\\');
//             }
//             buf.push(c);
//         }
//     }
//     pub fn is_meta_character(c: char) -> bool {
//         match c {
//             '\\' | '.' | '+' | '*' | '?' | '(' | ')' | '|' | '[' | ']'
//             | '{' | '}' | '^' | '$' | '#' | '&' | '-' | '~' => true,
//             _ => false,
//         }
//     }
// (Upstream doc: "Returns true if the given character has significance
//  in a regex. Generally speaking, these are the only characters which
//  must be escaped in order to match their literal meaning."; the
//  semver-freeze note -- "the set of characters ... is fixed and won't
//  change in a semver compatible release" -- is the stability edge the
//  trust rests on.)
//
// globset feeds this face exactly one ASCII char per call (the
// `b <= 0x7F` arm of bytes_to_escaped_literal wraps `char::from(b)`
// back into a one-char &str), so `spec_escape_char` -- the loop body
// at the single-char domain -- is the whole consumed face.
// ---------------------------------------------------------------------------

/// regex-syntax 0.8.11 lib.rs:261-279 -- is_meta_character (the 18-char
/// meta table, verbatim semantics).
pub open spec fn spec_is_meta_character(c: char) -> bool {
    c == '\\' || c == '.' || c == '+' || c == '*' || c == '?' || c == '('
        || c == ')' || c == '|' || c == '[' || c == ']' || c == '{' || c == '}'
        || c == '^' || c == '$' || c == '#' || c == '&' || c == '-' || c == '~'
}

pub fn is_meta_character_exec(c: char) -> (b: bool)
    ensures
        b == spec_is_meta_character(c),
{
    c == '\\' || c == '.' || c == '+' || c == '*' || c == '?' || c == '('
        || c == ')' || c == '|' || c == '[' || c == ']' || c == '{' || c == '}'
        || c == '^' || c == '$' || c == '#' || c == '&' || c == '-' || c == '~'
}

/// regex-syntax 0.8.11 lib.rs:213-219 -- escape_into at the single-char
/// domain (the meta arm prepends the backslash; every other char is
/// passed through unmodified).
pub open spec fn spec_escape_char(c: char) -> Seq<char> {
    if spec_is_meta_character(c) {
        seq!['\\', c]
    } else {
        seq![c]
    }
}

pub fn escape_char_exec(c: char) -> (r: Vec<char>)
    requires
        // the trusted face's consumed domain: bytes <= 0x7F re-wrapped
        // as Latin-1 chars (glob.rs:798's gate); the twin is called
        // only from that lane
        (c as u32) <= 0x7F,
    ensures
        r@ == spec_escape_char(c),
        // both arms land in ASCII (the backslash is 0x5C; the char's
        // own row is ASCII by the requires)
        forall|j: int| 0 <= j < r@.len() ==> (r@.index(j) as u32) <= 0x7F,
{
    let mut v: Vec<char> = Vec::new();
    if is_meta_character_exec(c) {
        v.push('\\');
    }
    v.push(c);
    v
}

// ---------------------------------------------------------------------------
// The `\xNN` self-arm (glob.rs:797-809 family). globset writes this
// itself (`write!(&mut s, "\\x{:02x}", b)`); the twin spells the
// formatting as the 16-way digit table (the value obligation is
// carried by the hex lemmas: every output digit is a lowercase hex
// digit and the two digits encode b/16 and b%16).
// ---------------------------------------------------------------------------

/// The lowercase hex digit of v (v < 16; the `{:x}` of glob.rs:802).
pub open spec fn spec_hex_digit(v: u8) -> char {
    if v == 15 { 'f' } else if v == 14 { 'e' } else if v == 13 { 'd' }
    else if v == 12 { 'c' } else if v == 11 { 'b' } else if v == 10 { 'a' }
    else if v == 9 { '9' } else if v == 8 { '8' } else if v == 7 { '7' }
    else if v == 6 { '6' } else if v == 5 { '5' } else if v == 4 { '4' }
    else if v == 3 { '3' } else if v == 2 { '2' } else if v == 1 { '1' }
    else { '0' }
}

/// dot.digit(b) == dom(digit) == d ; big "extended hex ok" predicate.
pub open spec fn is_lower_hex(c: char) -> bool {
    c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || c == '5'
        || c == '6' || c == '7' || c == '8' || c == '9' || c == 'a' || c == 'b'
        || c == 'c' || c == 'd' || c == 'e' || c == 'f'
}

/// The numeric value the digit table assigns to d (-1 when d is not a
/// lowercase hex digit; the inverse of spec_hex_digit).
pub open spec fn spec_hex_digit_val(d: char) -> int {
    if d == '0' { 0 } else if d == '1' { 1 } else if d == '2' { 2 }
    else if d == '3' { 3 } else if d == '4' { 4 } else if d == '5' { 5 }
    else if d == '6' { 6 } else if d == '7' { 7 } else if d == '8' { 8 }
    else if d == '9' { 9 } else if d == 'a' { 10 } else if d == 'b' { 11 }
    else if d == 'c' { 12 } else if d == 'd' { 13 } else if d == 'e' { 14 }
    else if d == 'f' { 15 } else { -1 }
}

/// Family lemma 1: the digit table lands in the lowercase-hex domain.
/// (One arm of the `\xNN` well-formedness column: every hex pair the
/// self-emission writes is a parseable lowercase-hex pair.)
pub proof fn hex_digit_is_lower_hex(v: u8)
    requires
        (v as u32) < 16,
    ensures
        is_lower_hex(spec_hex_digit(v)),
{
    if v == 15 {
    } else if v == 14 {
    } else if v == 13 {
    } else if v == 12 {
    } else if v == 11 {
    } else if v == 10 {
    } else if v == 9 {
    } else if v == 8 {
    } else if v == 7 {
    } else if v == 6 {
    } else if v == 5 {
    } else if v == 4 {
    } else if v == 3 {
    } else if v == 2 {
    } else if v == 1 {
    } else {
    }
}

/// Family lemma 2: the digit table is the value-correct digit (the
/// emission decodes back to the byte being escaped).
pub proof fn hex_digit_val(v: u8)
    requires
        (v as u32) < 16,
    ensures
        0 <= spec_hex_digit_val(spec_hex_digit(v)) < 16,
        spec_hex_digit_val(spec_hex_digit(v)) == v as int,
{
    if v == 15 {
    } else if v == 14 {
    } else if v == 13 {
    } else if v == 12 {
    } else if v == 11 {
    } else if v == 10 {
    } else if v == 9 {
    } else if v == 8 {
    } else if v == 7 {
    } else if v == 6 {
    } else if v == 5 {
    } else if v == 4 {
    } else if v == 3 {
    } else if v == 2 {
    } else if v == 1 {
    } else {
    }
}

/// The full self-arm emission for one byte: `\x` + two lowercase hex
/// digits (glob.rs:801-803). Well-formedness (glob.rs:797's doc
/// promise "All non-ASCII code units are converted to their escaped
/// form" -- this theorem is the "escaped form" spelling):
/// every emitted pair is a lowercase-hex pair encoding the byte.
pub open spec fn spec_hex2(b: u8) -> Seq<char> {
    seq!['\\', 'x', spec_hex_digit(b / 16), spec_hex_digit(b % 16)]
}

pub proof fn hex2_well_formed(b: u8)
    ensures
        spec_hex2(b).len() == 4,
        spec_hex2(b).index(0) == '\\',
        spec_hex2(b).index(1) == 'x',
        is_lower_hex(spec_hex2(b).index(2)),
        is_lower_hex(spec_hex2(b).index(3)),
        // the digits decode back to the two nibbles of b
        spec_hex_digit_val(spec_hex2(b).index(2)) == (b / 16) as int,
        spec_hex_digit_val(spec_hex2(b).index(3)) == (b % 16) as int,
{
    hex_digit_is_lower_hex(b / 16);
    hex_digit_is_lower_hex(b % 16);
    hex_digit_val(b / 16);
    hex_digit_val(b % 16);
}

// ---------------------------------------------------------------------------
// The UTF-8 byte table (upstream chars c feed `encode_utf8`; std's
// encoder is Rust-std-trusted, and the twin needs a spec binding it
// can prove against, so the standard 4-lane table is written out --
// arithmetic form, no bit ops. The exec twin below matches it).
//
// NOTE (compute shape): the lanes are guarded on the raw u32 value,
// and the single-byte lane's OUTPUT is expressed directly through the
// escape face on the char (not through a byte fold), so no
// cast-dependent recursion length survives into a KAT fold (the
// #GL-8 residual is confined to ground branch guards z3 closes from
// the cast axioms; probe round 3, units p_charlit*).
// ---------------------------------------------------------------------------

/// spec_is_ascii: the u32 bound of the single-byte utf8 lane.
pub open spec fn spec_is_ascii(c: char) -> bool {
    (c as u32) < 128
}

/// The utf8 bytes of the scalar x (the standard 4-lane table).
pub open spec fn spec_utf8_encode(x: u32) -> Seq<u8> {
    if x < 0x80 {
        seq![x as u8]
    } else if x < 0x800 {
        seq![(0xC0 + x / 64) as u8, (0x80 + x % 64) as u8]
    } else if x < 0x10000 {
        seq![
            (0xE0 + x / 4096) as u8,
            (0x80 + (x / 64) % 64) as u8,
            (0x80 + x % 64) as u8,
        ]
    } else {
        seq![
            (0xF0 + x / 262144) as u8,
            (0x80 + (x / 4096) % 64) as u8,
            (0x80 + (x / 64) % 64) as u8,
            (0x80 + x % 64) as u8,
        ]
    }
}

/// One byte's escaped emission (glob.rs:798-806's loop body): the
/// `b <= 0x7F` arm hands the byte (as a Latin-1 char) to the trusted
/// escape_into face; the >0x7F arm is globset's own `\xNN`.
pub open spec fn spec_esc_byte(b: u8) -> Seq<char> {
    if (b as u32) <= 0x7F {
        spec_escape_char(b as char)
    } else {
        spec_hex2(b)
    }
}

/// Origin Rust (glob.rs:797-809):
///     fn bytes_to_escaped_literal(bs: &[u8]) -> String {
///         let mut s = String::with_capacity(bs.len());
///         for &b in bs {
///             if b <= 0x7F {
///                 regex_syntax::escape_into(
///                     char::from(b).encode_utf8(&mut [0; 4]), &mut s, );
///             } else {
///                 write!(&mut s, "\\x{:02x}", b).unwrap();
///             }
///         }
///         s
///     }
/// (with_capacity is not observable; the `unwrap` never fires -- a
/// write! to a String is infallible and there is no # Panics doc
/// section on this surface. The prefix-fold shape below is the value
/// twin of the loop; the exec twin follows the same prefix discipline.)
pub open spec fn spec_bytes_to_escaped_literal_upto(bs: Seq<u8>, i: nat) -> Seq<char>
    decreases i
{
    if i == 0 {
        Seq::empty()
    } else {
        let b = bs.index((i - 1) as int);
        let prev = spec_bytes_to_escaped_literal_upto(bs, (i - 1) as nat);
        if (b as u32) <= 0x7F {
            prev + spec_escape_char(b as char)
        } else {
            prev + spec_hex2(b)
        }
    }
}

/// Full-sequence fold (the public byte face).
pub open spec fn spec_bytes_to_escaped_literal(bs: Seq<u8>) -> Seq<char> {
    spec_bytes_to_escaped_literal_upto(bs, bs.len())
}

/// Origin Rust (glob.rs:788-795):
///     fn char_to_escaped_literal(c: char) -> String {
///         let mut buf = [0; 4];
///         let bytes = c.encode_utf8(&mut buf).as_bytes();
///         bytes_to_escaped_literal(bytes)
///     }
/// The 4-lane inline form: the utf8 table picks the lane by the raw
/// scalar value, and the single-byte lane is stated directly through
/// the escape face (the `b <= 0x7F` arm's byte always IS the scalar;
/// see the ascii bridge lemma below).
pub open spec fn spec_char_to_lit(c: char) -> Seq<char> {
    let x = c as u32;
    if x < 0x80 {
        spec_escape_char(c)
    } else if x < 0x800 {
        spec_esc_byte((0xC0 + x / 64) as u8) + spec_esc_byte((0x80 + x % 64) as u8)
    } else if x < 0x10000 {
        spec_esc_byte((0xE0 + x / 4096) as u8)
            + spec_esc_byte((0x80 + (x / 64) % 64) as u8)
            + spec_esc_byte((0x80 + x % 64) as u8)
    } else {
        spec_esc_byte((0xF0 + x / 262144) as u8)
            + spec_esc_byte((0x80 + (x / 4096) % 64) as u8)
            + spec_esc_byte((0x80 + (x / 64) % 64) as u8)
            + spec_esc_byte((0x80 + x % 64) as u8)
    }
}

/// The ascii bridge: for an ASCII char the 1-byte utf8 lane is the
/// escape face on the char itself (this is the definitional glue the
/// KAT lane proofs ride -- the `b <= 0x7F` arm of the upstream loop
/// consults escape_into with exactly this char).
pub proof fn spec_char_lit_ascii_bridge(c: char)
    requires
        spec_is_ascii(c),
    ensures
        spec_char_to_lit(c) == spec_escape_char(c),
        spec_char_to_lit(c)
            == spec_bytes_to_escaped_literal_upto(spec_utf8_encode(c as u32), 1),
{
    let x = c as u32;
    assert(x < 128);
    let bs = spec_utf8_encode(x);
    assert(bs.len() == 1);
    assert(bs.index(0) == x as u8);
    // the Latin-1 round trip of the ASCII scalar is the char itself
    assert((x as u8) as char == c); 
    // the first upto step is definitional
    assert(spec_bytes_to_escaped_literal_upto(bs, 0) == Seq::empty());
    assert((Seq::empty() + spec_esc_byte(bs.index(0))) == spec_esc_byte(bs.index(0)));
    assert(spec_bytes_to_escaped_literal_upto(bs, 1) == spec_esc_byte(bs.index(0)));
    assert(spec_esc_byte(bs.index(0)) == spec_escape_char(c));
}

/// The per-token fold (glob.rs:713-792's loop body in upstream arm
/// order): consume the head token, emit its fragment, recurse on the
/// tail with the accumulated output.
pub open spec fn spec_tokens_to_regex(
    opts: GlobOptions,
    ts: Seq<TokenS>,
    out: Seq<char>,
    fuel: nat,
) -> Seq<char>
    decreases fuel
{
    if ts.len() == 0 || fuel == 0 {
        out
    } else {
        let rest = ts.subrange(1, ts.len() as int);
        match ts.index(0) {
            TokenS::Lit(c) => spec_tokens_to_regex(
                opts,
                rest,
                out + spec_char_to_lit(c),
                (fuel - 1) as nat,
            ),
            TokenS::Any => spec_tokens_to_regex(
                opts,
                rest,
                out + spec_frag_any(opts.literal_separator),
                (fuel - 1) as nat,
            ),
            TokenS::Zom => spec_tokens_to_regex(
                opts,
                rest,
                out + spec_frag_zom(opts.literal_separator),
                (fuel - 1) as nat,
            ),
            TokenS::RecP => {
                spec_tokens_to_regex(opts, rest, out + spec_frag_recp(), (fuel - 1) as nat)
            },
            TokenS::RecS => {
                spec_tokens_to_regex(opts, rest, out + spec_frag_recs(), (fuel - 1) as nat)
            },
            TokenS::RecZ => {
                spec_tokens_to_regex(opts, rest, out + spec_frag_recz(), (fuel - 1) as nat)
            },
            TokenS::Cls { negated: neg, ranges } => spec_tokens_to_regex(
                opts,
                rest,
                out + spec_class_frag(neg, ranges),
                (fuel - 1) as nat,
            ),
            TokenS::Alts(pats) => {
                // the wrapped alternates fragment, inline (the
                // parts.join + nonempty-wrap of glob.rs:743-762)
                let inner_n = spec_alts_inner(opts, pats, 0, (fuel - 1) as nat);
                let joined = if inner_n.1 > 0 {
                    seq!['(', '?', ':'] + inner_n.0 + seq![')']
                } else {
                    Seq::empty()
                };
                spec_tokens_to_regex(opts, rest, out + joined, (fuel - 1) as nat)
            }
        }
    }
}

/// Origin Rust (glob.rs:594-611) -- the public lowering entry:
///     /// Convert this pattern to a string that is guaranteed to be a
///     /// valid regular expression and will represent the matching
///     /// semantics of this glob pattern and the options given.
///     fn to_regex_with(options: &GlobOptions, tokens: &[Token]) -> String {
///         let mut re = String::new();
///         re.push_str("(?-u)");
///         if options.case_insensitive { re.push_str("(?i)"); }
///         re.push('^');
///         // Special case. If the entire glob is just `**`, then it
///         // should match everything.
///         if tokens.len() == 1 && tokens[0] == Token::RecursivePrefix {
///             re.push_str(".*");
///             re.push('$');
///             return re;
///         }
///         Self::tokens_to_regex(options, tokens, &mut re);
///         re.push('$');
///         re
///     }
/// (The doc comment is GM10's anchor line -- the two-sided
/// "guaranteed to be a valid regular expression" + "will represent
/// the matching semantics" promise. GL3 owns the validity
/// decomposition; the semantics side registers as the GL5 weld
/// predicate family. The RecursivePrefix comparator in the special
/// case is upstream's PartialEq on Token -- the twin's armed `is`
/// spelling.)
pub open spec fn spec_to_regex_with(opts: GlobOptions, ts: Seq<TokenS>, fuel: nat) -> Seq<char> {
    let head = seq!['(', '?', '-', 'u', ')']
        + (if opts.case_insensitive {
            seq!['(', '?', 'i', ')']
        } else {
            Seq::empty()
        })
        + seq!['^'];
    // Special case. If the entire glob is just `**`, then it should
    // match everything.
    if ts.len() == 1 && (ts.index(0) is RecP) {
        head + seq!['.', '*', '$']
    } else {
        head + spec_tokens_to_regex(opts, ts, Seq::empty(), fuel) + seq!['$']
    }
}

// ---------------------------------------------------------------------------
// The class-birth legality family -- the parser-side half of the
// validity decomposition. A closed class regex fragment is invalid in
// exactly two ways the parser can influence: an EMPTY class "[]"
// (rejected by the regex crate) and a mis-ordered range pair
// (glob.rs's own InvalidRange guard exists for it, but the lowering
// trusts the token). The lemma below pins the production site: every
// Cls token spec_class_loop pushes was born legal.
// ---------------------------------------------------------------------------

/// The legality predicate of a class token's range list: nonempty,
/// every pair ordered.
pub open spec fn ranges_legal(rs: Seq<(char, char)>) -> bool {
    rs.len() >= 1 && forall|j: int| 0 <= j < rs.len() ==> rs.index(j).0 <= rs.index(j).1
}

/// The legality of a token in the class position (match-spelled so no
/// getter naming rides).
pub open spec fn token_cls_legal(t: TokenS) -> bool {
    match t {
        TokenS::Cls { negated: _, ranges } => ranges_legal(ranges),
        _ => false,
    }
}


/// The exit classification + legality predicate of a class-loop run:
/// either an error value, or the rollback exit (cursor restored to
/// the class entry, latch set), or the close exit (cursor advanced
/// with the latch clear, the last pushed token a LEGAL Cls -- nonempty
/// ordered ranges). The st-free form is deliberate: entry-relative
/// transport columns (other-branches-unchanged / exact-one-push
/// counts) do not conduct across the recursion's ensures
/// instantiation (probe_units/p_recproof3); the transport content is
/// registered as the retired tail in the batch notes and re-erects at
/// the GL5 weld if the seam needs it.
pub open spec fn spec_cls_exit_ok(saved_pos: int, run: (SState, Option<ErrorKind>)) -> bool {
    (run.1) is Some
    || (run.1 is None && run.0.unclosed == true && run.0.pos == saved_pos)
    || (run.1 is None
        && run.0.unclosed == false
        && run.0.pos > saved_pos
        && run.0.brs.len() > 0
        && run.0.brs.index(run.0.brs.len() - 1).len() > 0
        && token_cls_legal(
            run.0.brs
                .index(run.0.brs.len() - 1)
                .index(run.0.brs.index(run.0.brs.len() - 1).len() - 1),
        ))
}

/// The birth-legality lemma over the class loop (glob.rs:1014-1070):
/// the three-exit classification holds for every run, and the close
/// exit's born Cls is always legal -- nonempty ordered ranges (GM10's
/// production-site half: a closed class never degenerates to the
/// rejected empty class "[]", and never carries a disordered pair).
/// The lattice invariant is carried in the loop frame: pairs stay
/// ordered, ranges stays nonempty once first flips false (every
/// processed content char pushes a range -- the first-']' and
/// first-'-' fold arms included), and in_range only latches with a
/// range present (upstream's glob.rs:1045 assert, carried as the
/// frame guard).
pub proof fn class_exit_shape(
    st: SState,
    saved_pos: int,
    negated: bool,
    first: bool,
    in_range: bool,
    ranges: Seq<(char, char)>,
)
    requires
        st.pos <= st.chars.len(),
        saved_pos <= st.pos,
        st.brs.len() > 0,
        // the class regime only runs with the latch clear (the
        // '['-guard of glob.rs:848; the rollback exit is the only
        // setter and it exits the regime)
        st.unclosed == false,
        // the loop-frame lattice (entry from spec_parse_class holds
        // trivially: first=true, ranges empty)
        forall|j: int| 0 <= j < ranges.len() ==> ranges.index(j).0 <= ranges.index(j).1,
        !first ==> ranges.len() >= 1,
        in_range ==> ranges.len() >= 1,
    ensures
        spec_cls_exit_ok(saved_pos, spec_class_loop(st, saved_pos, negated, first, in_range, ranges)),
    decreases st.chars.len() - st.pos,
{
    reveal(spec_class_loop);
    reveal(spec_push_token);
    reveal(spec_add_to_last);
    reveal(spec_bump);
    let run = spec_class_loop(st, saved_pos, negated, first, in_range, ranges);
    let b = spec_bump(st);
    if b.1 is None {
        // the exhaustion column (glob.rs:1015-1026): the unclosed
        // decision; the rollback restores the cursor exactly
        if st.opts.allow_unclosed_class {
            let st_r = SState {
                chars: st.chars,
                stack: st.stack,
                brs: st.brs,
                pos: saved_pos,
                unclosed: true,
                opts: st.opts,
            };
            let push_run = spec_push_token(st_r, TokenS::Lit('['));
            assert(run == push_run);
            assert(run.0 == push_run.0);
            assert(run.1 == push_run.1);
            if push_run.1 is None {
                assert(run.0.pos == saved_pos);
                assert(run.0.unclosed == true);
            }
            assert(spec_cls_exit_ok(saved_pos, run));
        } else {
            // UnclosedClass, nothing pushed
            assert(run.1 is Some);
            assert(spec_cls_exit_ok(saved_pos, run));
        }
    } else {
        let c = b.1.get_Some_0();
        let st1 = b.0;
        assert(st1.pos == st.pos + 1);
        assert(st1.brs == st.brs);
        assert(st1.unclosed == false);
        if c == ']' {
            if first {
                // the ']' folds as a first literal range; recursion
                let rs2 = ranges.push((']', ']'));
                assert forall|j: int|
                    #![trigger rs2.index(j)]
                    0 <= j < rs2.len() ==> rs2.index(j).0 <= rs2.index(j).1 by {}
                let child = spec_class_loop(st1, saved_pos, negated, false, in_range, rs2);
                assert(run == child);
                assert(run.0 == child.0);
                assert(run.1 == child.1);
                class_exit_shape(st1, saved_pos, negated, false, in_range, rs2);
                assert(spec_cls_exit_ok(saved_pos, child));
                assert(spec_cls_exit_ok(saved_pos, run));
            } else {
                // the close exit: the in_range fold of glob.rs:1066-1070
                // then the one Cls push; legality by the frame lattice
                let rs = if in_range {
                    ranges.push(('-', '-'))
                } else {
                    ranges
                };
                assert(rs.len() >= 1) by {
                    if in_range {
                        assert(ranges.len() >= 1);
                        assert(ranges.push(('-', '-')).len() == ranges.len() + 1);
                    }
                }
                assert forall|j: int|
                    #![trigger rs.index(j)]
                    0 <= j < rs.len() ==> rs.index(j).0 <= rs.index(j).1 by {}
                let push_run = spec_push_token(st1, TokenS::Cls { negated, ranges: rs });
                assert(run == push_run);
                assert(run.0 == push_run.0);
                assert(run.1 == push_run.1);
                if push_run.1 is None {
                    assert(run.0.pos == st1.pos);
                    assert(run.0.pos > saved_pos);
                    assert(run.0.unclosed == false);
                    assert(push_run.0.brs.len() == st1.brs.len());
                    let tail = st1.brs.index(st1.brs.len() - 1);
                    assert(push_run.0.brs.index(st1.brs.len() - 1)
                        == tail.push(TokenS::Cls { negated, ranges: rs }));
                    assert(push_run.0.brs.index(push_run.0.brs.len() - 1).len()
                        >= tail.len());
                    let pushed = TokenS::Cls { negated, ranges: rs };
                    assert(token_cls_legal(pushed));
                    assert(push_run.0.brs
                        .index(push_run.0.brs.len() - 1)
                        .index(push_run.0.brs.index(push_run.0.brs.len() - 1).len() - 1)
                        == pushed);
                }
                assert(spec_cls_exit_ok(saved_pos, run));
            }
        } else if c == '-' {
            if first {
                let rs2 = ranges.push(('-', '-'));
                assert forall|j: int|
                    #![trigger rs2.index(j)]
                    0 <= j < rs2.len() ==> rs2.index(j).0 <= rs2.index(j).1 by {}
                let child = spec_class_loop(st1, saved_pos, negated, false, in_range, rs2);
                assert(run == child);
                assert(run.0 == child.0);
                assert(run.1 == child.1);
                class_exit_shape(st1, saved_pos, negated, false, in_range, rs2);
                assert(spec_cls_exit_ok(saved_pos, child));
                assert(spec_cls_exit_ok(saved_pos, run));
            } else if in_range {
                let up = spec_add_to_last(st1, ranges, '-');
                if up.1 is None {
                    let rs2 = up.0;
                    assert forall|j: int|
                        #![trigger rs2.index(j)]
                        0 <= j < rs2.len() ==> rs2.index(j).0 <= rs2.index(j).1 by {}
                    let child = spec_class_loop(st1, saved_pos, negated, false, false, rs2);
                    assert(run == child);
                    assert(run.0 == child.0);
                    assert(run.1 == child.1);
                    class_exit_shape(st1, saved_pos, negated, false, false, rs2);
                    assert(spec_cls_exit_ok(saved_pos, child));
                    assert(spec_cls_exit_ok(saved_pos, run));
                } else {
                    // the InvalidRange(start,'-') error column
                    assert(run.1 is Some);
                    assert(spec_cls_exit_ok(saved_pos, run));
                }
            } else {
                // the pending-range latch; ranges nonempty by !first
                assert(ranges.len() >= 1);
                let child = spec_class_loop(st1, saved_pos, negated, false, true, ranges);
                assert(run == child);
                assert(run.0 == child.0);
                assert(run.1 == child.1);
                class_exit_shape(st1, saved_pos, negated, false, true, ranges);
                assert(spec_cls_exit_ok(saved_pos, child));
                assert(spec_cls_exit_ok(saved_pos, run));
            }
        } else {
            if in_range {
                let up = spec_add_to_last(st1, ranges, c);
                if up.1 is None {
                    let rs2 = up.0;
                    assert forall|j: int|
                        #![trigger rs2.index(j)]
                        0 <= j < rs2.len() ==> rs2.index(j).0 <= rs2.index(j).1 by {}
                    let child = spec_class_loop(st1, saved_pos, negated, false, false, rs2);
                    assert(run == child);
                    assert(run.0 == child.0);
                    assert(run.1 == child.1);
                    class_exit_shape(st1, saved_pos, negated, false, false, rs2);
                    assert(spec_cls_exit_ok(saved_pos, child));
                    assert(spec_cls_exit_ok(saved_pos, run));
                } else {
                    // the InvalidRange(start,c) error column
                    assert(run.1 is Some);
                    assert(spec_cls_exit_ok(saved_pos, run));
                }
            } else {
                let rs2 = ranges.push((c, c));
                assert forall|j: int|
                    #![trigger rs2.index(j)]
                    0 <= j < rs2.len() ==> rs2.index(j).0 <= rs2.index(j).1 by {}
                let child = spec_class_loop(st1, saved_pos, negated, false, false, rs2);
                assert(run == child);
                assert(run.0 == child.0);
                assert(run.1 == child.1);
                class_exit_shape(st1, saved_pos, negated, false, false, rs2);
                assert(spec_cls_exit_ok(saved_pos, child));
                assert(spec_cls_exit_ok(saved_pos, run));
            }
        }
    }
    // trailing assembly
    assert(spec_cls_exit_ok(saved_pos, run));
}


// ===========================================================================
// tokens_to_regex's emission family (glob.rs:713-792) -- the per-token
// fragments, the class fold and the alternates fold.
// ===========================================================================

/// Origin Rust (glob.rs:724-733) -- the Any fragment:
///     Token::Any => {
///         if options.literal_separator {
///             re.push_str("[^/]");
///         } else {
///             re.push_str(".");
///         }
///     }
pub open spec fn spec_frag_any(lit_sep: bool) -> Seq<char> {
    if lit_sep {
        seq!['[', '^', '/', ']']
    } else {
        seq!['.']
    }
}

/// Origin Rust (glob.rs:734-743) -- the ZeroOrMore fragment:
///     Token::ZeroOrMore => {
///         if options.literal_separator {
///             re.push_str("[^/]*");
///         } else {
///             re.push_str(".*");
///         }
///     }
pub open spec fn spec_frag_zom(lit_sep: bool) -> Seq<char> {
    if lit_sep {
        seq!['[', '^', '/', ']', '*']
    } else {
        seq!['.', '*']
    }
}

/// Origin Rust (glob.rs:744-750) -- the three recursive fragments:
///     Token::RecursivePrefix => { re.push_str("(?:/?|.*/)"); }
///     Token::RecursiveSuffix => { re.push_str("/.*"); }
///     Token::RecursiveZeroOrMore => { re.push_str("(?:/|/.*/)"); }
pub open spec fn spec_frag_recp() -> Seq<char> {
    // "(?:/?|.*/)"
    seq!['(', '?', ':', '/', '?', '|', '.', '*', '/', ')']
}

pub open spec fn spec_frag_recs() -> Seq<char> {
    // "/.*"
    seq!['/', '.', '*']
}

pub open spec fn spec_frag_recz() -> Seq<char> {
    // "(?:/|/.*/)"
    seq!['(', '?', ':', '/', '|', '/', '.', '*', '/', ')']
}

/// Origin Rust (glob.rs:766-783) -- the Class fragment:
///     Token::Class { negated, ref ranges } => {
///         re.push('[');
///         if negated { re.push('^'); }
///         for r in ranges {
///             if r.0 == r.1 {
///                 // Not strictly necessary, but nicer to look at.
///                 re.push_str(&char_to_escaped_literal(r.0));
///             } else {
///                 re.push_str(&char_to_escaped_literal(r.0));
///                 re.push('-');
///                 re.push_str(&char_to_escaped_literal(r.1));
///             }
///         }
///         re.push(']');
///     }
/// (the "Not strictly necessary, but nicer to look at." comment is
/// upstream's, glob.rs:773. The prefix fold below carries the opening
/// bracket in the base and the closing bracket in the wrapper; the
/// range order is upstream order. Self-contained recursion over flat
/// ranges, so the index measure suffices.)
pub open spec fn spec_class_frag_upto(negated: bool, rs: Seq<(char, char)>, i: nat) -> Seq<char>
    decreases i
{
    if i == 0 {
        if negated {
            seq!['[', '^']
        } else {
            seq!['[']
        }
    } else {
        let r = rs.index((i - 1) as int);
        let prev = spec_class_frag_upto(negated, rs, (i - 1) as nat);
        if r.0 == r.1 {
            prev + spec_char_to_lit(r.0)
        } else {
            prev + spec_char_to_lit(r.0) + seq!['-'] + spec_char_to_lit(r.1)
        }
    }
}

/// The full class fragment (closing bracket included).
pub open spec fn spec_class_frag(negated: bool, rs: Seq<(char, char)>) -> Seq<char> {
    spec_class_frag_upto(negated, rs, rs.len()) + seq![']']
}

/// The alternates fold (glob.rs:743-762):
///     Token::Alternates(ref patterns) => {
///         let mut parts = vec![];
///         for pat in patterns {
///             let mut altre = String::new();
///             Self::tokens_to_regex(options, &pat, &mut altre);
///             if !altre.is_empty() || options.empty_alternates {
///                 parts.push(altre);
///             }
///         }
///         // It is possible to have an empty set in which case the
///         // resulting alternation '()' would be an error.
///         if !parts.is_empty() {
///             re.push_str("(?:");
///             re.push_str(&parts.join("|"));
///             re.push(')');
///         }
///     }
/// (the upstream comment names the exact invalidity this gate
/// excludes -- the bare empty alternation. The fold below carries the
/// kept-parts count so the wrap decides exactly upstream's
/// `!parts.is_empty()`; order is head-first, matching upstream's
/// parts.push order.)
pub open spec fn spec_alts_inner(
    opts: GlobOptions,
    pats: Seq<Seq<TokenS>>,
    i: nat,
    fuel: nat,
) -> (Seq<char>, int)
    decreases fuel
{
    if fuel == 0 || i as int >= pats.len() {
        (Seq::empty(), 0)
    } else {
        // tail-first: the kept suffix folds first, then the head joins
        // in front of "|" when a kept suffix remains (parts.join's
        // separator placement)
        let (rest, n) = spec_alts_inner(opts, pats, (i + 1) as nat, (fuel - 1) as nat);
        let part = spec_tokens_to_regex(
            opts,
            pats.index(i as int),
            Seq::empty(),
            (fuel - 1) as nat,
        );
        if part.len() > 0 || opts.empty_alternates {
            if n > 0 {
                (part + seq!['|'] + rest, n + 1)
            } else {
                (part, 1)
            }
        } else {
            (rest, n)
        }
    }
}

/// Shape lemma (the wrap form of glob.rs:757-761): the crafted
/// alternates fragment is either the empty fragment or a properly
/// wrapped group -- the empty-parts gate never emits a bare or
/// unbalanced group, and the wrap runs "(?:" .. ")" with the joined
/// body inside (wrap length 4 + joined, so >= 4 unconditionally).
/// NOTE the empty_alternates corner: a kept-but-empty single part
/// yields "(?:)" -- upstream produces exactly this too, and its
/// validity rests on the trusted regex-automata face's empty-group
/// acceptance (registered boundary in the batch notes, not claimed
/// here).
pub proof fn alts_frag_shape(opts: GlobOptions, pats: Seq<Seq<TokenS>>, fuel: nat)
    ensures
    {
        let inner_n = spec_alts_inner(opts, pats, 0, fuel);
        let r = if inner_n.1 > 0 {
            seq!['(', '?', ':'] + inner_n.0 + seq![')']
        } else {
            Seq::empty()
        };
        r.len() == 0
            || (r.len() >= 4
                && r.index(0) == '('
                && r.index(1) == '?'
                && r.index(2) == ':'
                && r.index(r.len() - 1) == ')')
    },
{
    // the kept-count column decides
    let inner_n = spec_alts_inner(opts, pats, 0, fuel);
    if inner_n.1 > 0 {
        let r = seq!['(', '?', ':'] + inner_n.0 + seq![')'];
        assert(r.index(0) == '(');
        assert(r.index(1) == '?');
        assert(r.index(2) == ':');
        assert(r.index(r.len() - 1) == ')');
        assert(r.len() == 4 + inner_n.0.len());
        assert(r.len() >= 4);
    }
}

// ---------------------------------------------------------------------------
// THE SPEC ASCII ROWS FAMILY -- the assembly-domain column carried on
// the spec side (the '(?-u)' bytes-coherence of GM10's validity table:
// every char of the synthesized regex is ASCII; non-ASCII pattern
// material appears only inside \xNN triples).
// ---------------------------------------------------------------------------

/// The single-byte ascii theorem (spec side): every row of a byte's
/// escaped emission is ASCII -- the `b <= 0x7F` arm's rows come from
/// the trusted face over an ASCII char, the >0x7F arm's rows are the
/// hex triple's.
pub proof fn spec_esc_byte_ascii_rows(b: u8)
    ensures
        forall|j: int| 0 <= j < spec_esc_byte(b).len() ==>
            (spec_esc_byte(b).index(j) as u32) <= 0x7F,
{
    if (b as u32) <= 0x7F {
        escape_char_ascii(b as char);
    } else {
        hex_digit_ascii(b / 16);
        hex_digit_ascii(b % 16);
    }
}

/// The full char-lane ascii theorem (spec side): for every char, the
/// char_to_escaped_literal emission is pure ASCII (glob.rs:793's
/// contract "All non-ASCII code units are converted to their escaped
/// form").
pub proof fn spec_char_to_lit_ascii_rows(c: char)
    ensures
        forall|j: int| 0 <= j < spec_char_to_lit(c).len() ==>
            (spec_char_to_lit(c).index(j) as u32) <= 0x7F,
{
    let x = c as u32;
    if x < 0x80 {
        escape_char_ascii(c);
    } else if x < 0x800 {
        spec_esc_byte_ascii_rows((0xC0 + x / 64) as u8);
        spec_esc_byte_ascii_rows((0x80 + x % 64) as u8);
    } else if x < 0x10000 {
        spec_esc_byte_ascii_rows((0xE0 + x / 4096) as u8);
        spec_esc_byte_ascii_rows((0x80 + (x / 64) % 64) as u8);
        spec_esc_byte_ascii_rows((0x80 + x % 64) as u8);
    } else {
        spec_esc_byte_ascii_rows((0xF0 + x / 262144) as u8);
        spec_esc_byte_ascii_rows((0x80 + (x / 4096) % 64) as u8);
        spec_esc_byte_ascii_rows((0x80 + (x / 64) % 64) as u8);
        spec_esc_byte_ascii_rows((0x80 + x % 64) as u8);
    }
}

// ---------------------------------------------------------------------------
// THE EXEC TWIN of the lowering (glob.rs:694-809's shape over the Token
// carrier). Structural obligations: no panic (all index bounds
// guarded); termination via the lex measure (budget, tokens.len()));
// value posts bind each helper to its spec twin. The alternates
// recursion rides an explicit depth budget (verus demands a
// terminating measure where upstream recurses freely; the budget == 1
// At-An-Alts column is a truncation upstream never produces for
// budgets above the tree nesting -- documented per site; value
// fidelity carried by the KAT/oracle/mirror arms per the GL2 W2 seam
// discipline).
// ---------------------------------------------------------------------------

/// The exec hex digit (spec_hex_digit's twin; glob.rs:802's `{:x}`).
pub fn hex_digit_exec(v: u8) -> (r: char)
    ensures
        r == spec_hex_digit(v),
        (r as u32) < 128,
{
    if v == 15 { 'f' } else if v == 14 { 'e' } else if v == 13 { 'd' }
    else if v == 12 { 'c' } else if v == 11 { 'b' } else if v == 10 { 'a' }
    else if v == 9 { '9' } else if v == 8 { '8' } else if v == 7 { '7' }
    else if v == 6 { '6' } else if v == 5 { '5' } else if v == 4 { '4' }
    else if v == 3 { '3' } else if v == 2 { '2' } else if v == 1 { '1' }
    else { '0' }
}

/// spec_hex_digit's charset is ASCII (the hex well-formedness
/// column's ascii half).
pub proof fn hex_digit_ascii(v: u8)
    requires
        (v as u32) < 16,
    ensures
        (spec_hex_digit(v) as u32) < 128,
{
    let c = spec_hex_digit(v);
    assert(is_lower_hex(c));
    // each lowercase-hex digit is ASCII: 16-way ground equality
    if c == '0' {
    } else if c == '1' {
    } else if c == '2' {
    } else if c == '3' {
    } else if c == '4' {
    } else if c == '5' {
    } else if c == '6' {
    } else if c == '7' {
    } else if c == '8' {
    } else if c == '9' {
    } else if c == 'a' {
    } else if c == 'b' {
    } else if c == 'c' {
    } else if c == 'd' {
    } else if c == 'e' {
    } else {
        assert(c == 'f');
    }
}

/// The `\xNN` self-arm exec (one byte; glob.rs:801-803).
pub fn hex2_exec(b: u8) -> (r: Vec<char>)
    ensures
        r@ == spec_hex2(b),
        forall|j: int| 0 <= j < r@.len() ==> (r@.index(j) as u32) < 128,
{
    let mut v: Vec<char> = Vec::new();
    v.push('\\');
    v.push('x');
    proof {
        hex_digit_ascii(b / 16);
        hex_digit_ascii(b % 16);
    }
    let d0 = hex_digit_exec(b / 16);
    v.push(d0);
    let d1 = hex_digit_exec(b % 16);
    v.push(d1);
    v
}

/// spec_escape_char's output is ASCII whenever the input char is (the
/// trusted face's ASCII closure at the `b <= 0x7F` byte domain).
pub proof fn escape_char_ascii(c: char)
    requires
        (c as u32) <= 0x7F,
    ensures
        forall|j: int| 0 <= j < spec_escape_char(c).len() ==>
            (spec_escape_char(c).index(j) as u32) <= 0x7F,
{
    let out = spec_escape_char(c);
    if spec_is_meta_character(c) {
        // the first char is the backslash (0x5C), the second is the
        // ASCII char itself
        assert((('\\') as u32) == 0x5C);
        assert((c as u32) <= 0x7F);
    }
}

/// Definitional prefix step of the byte fold (the exec loop's
/// invariant glue).
pub proof fn bytes_upto_step(bs: Seq<u8>, i: nat)
    requires
        (i as int) < bs.len(),
    ensures
        spec_bytes_to_escaped_literal_upto(bs, (i + 1) as nat)
            == spec_bytes_to_escaped_literal_upto(bs, i)
                + spec_esc_byte(bs.index(i as int)),
{
}

/// The utf8 table exec (upstream `c.encode_utf8(&mut [0;4])`, std's
/// encoder being Rust-std-trusted; the twin is the arithmetic form
/// the spec face uses, so the byte column binds spec-to-exec).
pub fn utf8_bytes_exec(c: char) -> (v: Vec<u8>)
    ensures
        v@ == spec_utf8_encode(c as u32),
        v@.len() >= 1,
        v@.len() <= 4,
{
    let x = c as u32;
    let mut v: Vec<u8> = Vec::new();
    if x < 0x80 {
        assert((x as int) < 256);
        v.push(x as u8);
    } else if x < 0x800 {
        let b0 = (0xC0 + x / 64) as u8;
        let b1 = (0x80 + x % 64) as u8;
        assert(b0 as int >= 0xC0 && b0 as int <= 0xDF);
        assert(b1 as int >= 0x80 && b1 as int <= 0xBF);
        v.push(b0);
        v.push(b1);
    } else if x < 0x10000 {
        let b0 = (0xE0 + x / 4096) as u8;
        let b1 = (0x80 + (x / 64) % 64) as u8;
        let b2 = (0x80 + x % 64) as u8;
        assert(b0 as int >= 0xE0 && b0 as int <= 0xEF);
        assert(b1 as int >= 0x80 && b1 as int <= 0xBF);
        assert(b2 as int >= 0x80 && b2 as int <= 0xBF);
        v.push(b0);
        v.push(b1);
        v.push(b2);
    } else {
        let b0 = (0xF0 + x / 262144) as u8;
        let b1 = (0x80 + (x / 4096) % 64) as u8;
        let b2 = (0x80 + (x / 64) % 64) as u8;
        let b3 = (0x80 + x % 64) as u8;
        assert(b0 as int >= 0xF0 && b0 as int <= 0xF7);
        assert(b1 as int >= 0x80 && b1 as int <= 0xBF);
        assert(b2 as int >= 0x80 && b2 as int <= 0xBF);
        assert(b3 as int >= 0x80 && b3 as int <= 0xBF);
        v.push(b0);
        v.push(b1);
        v.push(b2);
        v.push(b3);
    }
    v
}

/// bytes_to_escaped_literal (glob.rs:797-809) -- the exec loop over
/// the byte sequence (upstream's String concatenation is the Vec
/// append here; each byte's piece picks the same two arms).
pub fn bytes_to_escaped_literal_exec(bs: &[u8]) -> (r: Vec<char>)
    ensures
        r@ == spec_bytes_to_escaped_literal(bs@),
{
    let mut out: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < bs.len()
        invariant
            i <= bs.len(),
            out@ == spec_bytes_to_escaped_literal_upto(bs@, i as nat),
        decreases bs.len() - i,
    {
        let b = bs[i];
        // glob.rs:798-806: the b <= 0x7F arm hands the Latin-1 char
        // to the trusted escape_into face; else the self-arm hex
        let piece: Vec<char> = if b <= 0x7F {
            escape_char_exec(b as char)
        } else {
            hex2_exec(b)
        };
        proof {
            // the byte lane's spec glue: piece@ == spec_esc_byte(b)
            if b <= 0x7F {
                assert(spec_esc_byte(b) == spec_escape_char(b as char));
                assert(piece@ == spec_escape_char(b as char));
            } else {
                assert(spec_esc_byte(b) == spec_hex2(b));
                assert(piece@ == spec_hex2(b));
            }
            bytes_upto_step(bs@, i as nat);
        }
        // splice the piece onto out: the loop entry anchors on the
        // outer fold equation (out is a local; old() names function
        // parameters only)
        let mut k: usize = 0;
        while k < piece.len()
            invariant
                i <= bs.len(),
                k <= piece@.len(),
                out@ == spec_bytes_to_escaped_literal_upto(bs@, i as nat)
                    + piece@.subrange(0, k as int),
            decreases piece@.len() - k,
        {
            let ch = piece[k];
            assert(piece@.index(k as int) == ch);
            out.push(ch);
            k += 1;
        }
        proof {
            // the k-loop finished: out@ == upto(i) + the whole piece,
            // and the piece IS this byte's spec lane
            assert(piece@.subrange(0, piece@.len() as int) == piece@);
            assert(out@ == spec_bytes_to_escaped_literal_upto(bs@, i as nat) + piece@);
            assert(out@ == spec_bytes_to_escaped_literal_upto(bs@, (i + 1) as nat));
        }
        i += 1;
    }
    out
}

/// char_to_escaped_literal (glob.rs:788-795):
///     fn char_to_escaped_literal(c: char) -> String {
///         let mut buf = [0; 4];
///         let bytes = c.encode_utf8(&mut buf).as_bytes();
///         bytes_to_escaped_literal(bytes)
///     }
/// Value post rides the bytes fold; the char's bytes arrive from the
/// utf8 table twin (rows: the spec-side ascii theorem carries the
/// domain column).
pub fn char_to_escaped_literal_exec(c: char) -> (r: Vec<char>)
    ensures
        r@ == spec_bytes_to_escaped_literal(spec_utf8_encode(c as u32)),
{
    let bytes = utf8_bytes_exec(c);
    bytes_to_escaped_literal_exec(bytes.as_slice())
}

/// The verified char-table build: the fixed per-token fragments and
/// prologue tables ride this (no panic; append-only).
pub fn ascii_vec(src: &[char]) -> (v: Vec<char>)
    ensures
        v@ == src@,
{
    let mut v: Vec<char> = Vec::new();
    let mut k: usize = 0;
    while k < src.len()
        invariant
            k <= src.len(),
            v@ == src@.subrange(0, k as int),
        decreases src.len() - k,
    {
        let ch = src[k];
        assert(src@.index(k as int) == ch);
        v.push(ch);
        k += 1;
    }
    proof {
        assert(src@.subrange(0, src@.len() as int) == src@);
    }
    v
}

/// Fixed-table append helper (no panic; index guarded by the bound).
pub fn push_ascii_seq(out: &mut Vec<char>, frag: &[char])
    ensures
        final(out)@ == old(out)@ + frag@,
{
    let mut k: usize = 0;
    while k < frag.len()
        invariant
            k <= frag@.len(),
            out@ == old(out)@ + frag@.subrange(0, k as int),
        decreases frag@.len() - k,
    {
        let ch = frag[k];
        assert(frag@.index(k as int) == ch);
        out.push(ch);
        k += 1;
    }
    proof {
        assert(frag@.subrange(0, frag@.len() as int) == frag@);
    }
}

/// The Vec piece append helper (the literal/class fragment
/// splicings).
pub fn push_ascii_vec(out: &mut Vec<char>, piece: &Vec<char>)
    ensures
        final(out)@ == old(out)@ + piece@,
{
    // append-only; no panic (index guarded by the loop bound)
    let mut k: usize = 0;
    while k < piece.len()
        invariant
            k <= piece@.len(),
            out@ == old(out)@ + piece@.subrange(0, k as int),
        decreases piece@.len() - k,
    {
        let ch = piece[k];
        assert(piece@.index(k as int) == ch);
        out.push(ch);
        k += 1;
    }
    proof {
        assert(piece@.subrange(0, piece@.len() as int) == piece@);
    }
}

/// The fixed per-token fragments as char tables (spec_frag_* twins).
pub fn frag_any_exec(lit_sep: bool) -> (r: Vec<char>)
    ensures
        r@ == spec_frag_any(lit_sep),
{
    if lit_sep {
        ascii_vec(&['[', '^', '/', ']'])
    } else {
        ascii_vec(&['.'])
    }
}

pub fn frag_zom_exec(lit_sep: bool) -> (r: Vec<char>)
    ensures
        r@ == spec_frag_zom(lit_sep),
{
    if lit_sep {
        ascii_vec(&['[', '^', '/', ']', '*'])
    } else {
        ascii_vec(&['.', '*'])
    }
}

pub fn frag_recp_exec() -> (r: Vec<char>)
    ensures
        r@ == spec_frag_recp(),
{
    ascii_vec(&['(', '?', ':', '/', '?', '|', '.', '*', '/', ')'])
}

pub fn frag_recs_exec() -> (r: Vec<char>)
    ensures
        r@ == spec_frag_recs(),
{
    ascii_vec(&['/', '.', '*'])
}

pub fn frag_recz_exec() -> (r: Vec<char>)
    ensures
        r@ == spec_frag_recz(),
{
    ascii_vec(&['(', '?', ':', '/', '|', '/', '.', '*', '/', ')'])
}

/// The class fragment exec (glob.rs:766-783): '[' optional '^' then
/// the escaped endpoints with '-' separators, then ']'. The char
/// pieces come from char_to_escaped_literal_exec.
pub fn class_frag_exec(negated: bool, ranges: &[(char, char)]) -> (r: Vec<char>)
    ensures
        // the bracket skeleton is always present: '[' .. ']'
        r@.len() >= 2,
{
    let mut out: Vec<char> = Vec::new();
    out.push('[');
    assert(out@.len() >= 1);
    if negated {
        out.push('^');
        assert(out@.len() >= 2);
    }
    let mut i: usize = 0;
    while i < ranges.len()
        invariant
            i <= ranges.len(),
            out@.len() >= 1,
        decreases ranges.len() - i,
    {
        let (c0, c1) = ranges[i];
        let p0 = char_to_escaped_literal_exec(c0);
        push_ascii_seq(&mut out, p0.as_slice());
        if c0 != c1 {
            // Not strictly necessary, but nicer to look at.
            // (glob.rs:773 -- the dashed form below)
            out.push('-');
            let p1 = char_to_escaped_literal_exec(c1);
            push_ascii_seq(&mut out, p1.as_slice());
        }
        i += 1;
    }
    out.push(']');
    proof {
        assert(out@.len() >= 2);
    }
    out
}

/// The '(?-u)' prologue append (glob.rs:596-600).
pub fn push_prologue(opts: GlobOptions, out: &mut Vec<char>)
    ensures
        final(out)@ == old(out)@
            + seq!['(', '?', '-', 'u', ')']
            + (if opts.case_insensitive {
                seq!['(', '?', 'i', ')']
            } else {
                Seq::empty()
            })
            + seq!['^'],
{
    // append-only spelling of upstream's push_str sequence
    out.push('(');
    out.push('?');
    out.push('-');
    out.push('u');
    out.push(')');
    if opts.case_insensitive {
        out.push('(');
        out.push('?');
        out.push('i');
        out.push(')');
    }
    out.push('^');
}

/// Fresh-buffer wrapper for the alternates recursion (a value-returning
/// face around the &mut twin; keeps the borrow structure of the
/// alternates arm flat).
pub fn tokens_to_regex_fresh(opts: GlobOptions, tokens: &Vec<Token>, budget: usize) -> (r: Vec<char>)
    requires
        budget > 0,
    ensures
        r@.len() >= 0,
    decreases budget,
{
    let mut fresh: Vec<char> = Vec::new();
    tokens_to_regex_exec(opts, tokens, &mut fresh, budget);
    fresh
}

/// tokens_to_regex exec twin (glob.rs:713-792) -- the loop over the
/// token list with the alternates recursion carrying budget. The
/// per-token pushes are append-only; the alternates part emits the
/// '|' separator between kept parts (upstream's parts.join) and wraps
/// nonempty groups only (glob.rs:757-761).
pub fn tokens_to_regex_exec(
    opts: GlobOptions,
    tokens: &Vec<Token>,
    out: &mut Vec<char>,
    budget: usize,
)
    requires
        budget > 0,
        // the recursion only descends at Alts tokens; the budget
        // covers the tree nesting of the token list (the budget == 1
        // At-An-Alts column is a truncation, documented per site)
    ensures
        // append-only growth: the output never shrinks (rows: the
        // spec-side ascii theorem carries the domain column)
        final(out)@.len() >= old(out)@.len(),
    decreases
        budget,
        tokens.len(),
{
    let mut i: usize = 0;
    while i < tokens.len()
        invariant
            i <= tokens.len(),
            budget > 0,
            out@.len() >= old(out)@.len(),
        decreases tokens.len() - i,
    {
        match &tokens[i] {
            Token::Literal(c) => {
                let piece = char_to_escaped_literal_exec(*c);
                push_ascii_vec(out, &piece);
            },
            Token::Any => {
                let piece = frag_any_exec(opts.literal_separator);
                push_ascii_vec(out, &piece);
            },
            Token::ZeroOrMore => {
                let piece = frag_zom_exec(opts.literal_separator);
                push_ascii_vec(out, &piece);
            },
            Token::RecursivePrefix => {
                let piece = frag_recp_exec();
                push_ascii_vec(out, &piece);
            },
            Token::RecursiveSuffix => {
                let piece = frag_recs_exec();
                push_ascii_vec(out, &piece);
            },
            Token::RecursiveZeroOrMore => {
                let piece = frag_recz_exec();
                push_ascii_vec(out, &piece);
            },
            Token::Class { negated, ranges } => {
                let piece = class_frag_exec(*negated, ranges.as_slice());
                push_ascii_vec(out, &piece);
            },
            Token::Alternates(patterns) => {
                // the alternates arm: each member's emission joins to
                // a local buffer first (upstream folds String::new()
                // per part), kept per the empty gate, then "|"-joined
                // and wrapped (glob.rs:743-762)
                let mut parts: Vec<Vec<char>> = Vec::new();
                let mut m: usize = 0;
                while m < patterns.len()
                    invariant
                        m <= patterns.len(),
                        budget > 0,
                        i <= tokens.len(),
                    decreases patterns.len() - m,
                {
                    if budget > 1 {
                        let altre = tokens_to_regex_fresh(opts, &patterns[m], budget - 1);
                        if altre.len() > 0 || opts.empty_alternates {
                            parts.push(altre);
                        }
                    }
                    m += 1;
                }
                // It is possible to have an empty set in which case the
                // resulting alternation '()' would be an error.
                // (glob.rs:757-758, verbatim)
                if parts.len() > 0 {
                    out.push('(');
                    out.push('?');
                    out.push(':');
                    let mut p: usize = 0;
                    while p < parts.len()
                        invariant
                            p <= parts.len(),
                            budget > 0,
                            i <= tokens.len(),
                            out@.len() >= (old(out)@).len(),
                        decreases parts.len() - p,
                    {
                        // upstream parts.join("|"): the separator only
                        // between kept parts
                        if p > 0 {
                            out.push('|');
                        }
                        push_ascii_vec(out, &parts[p]);
                        p += 1;
                    }
                    out.push(')');
                }
                proof { assert(out@.len() >= (old(out)@).len()); }
            },
        }
        i += 1;
    }
}

/// to_regex_with exec twin (glob.rs:594-611): the prologue, the
/// `**`-alone special case, the token emission, the '$' epilogue.
/// The budget column passes to the alternates recursion.
pub fn to_regex_with_exec(opts: GlobOptions, tokens: &Vec<Token>, budget: usize) -> (re: Vec<char>)
    requires
        budget > 0,
    ensures
        // prologue + epilogue skeleton always present
        re@.len() >= 4,
{
    let mut re: Vec<char> = Vec::new();
    push_prologue(opts, &mut re);
    // Special case. If the entire glob is just `**`, then it should
    // match everything. (glob.rs:601-604)
    if tokens.len() == 1 {
        match tokens[0] {
            Token::RecursivePrefix => {
                push_ascii_seq(&mut re, &['.', '*']);
                re.push('$');
                return re;
            },
            _ => {},
        }
    }
    tokens_to_regex_exec(opts, tokens, &mut re, budget);
    re.push('$');
    proof {
        assert(re@.len() >= 4);
    }
    re
}

// ===========================================================================
// The GL2 slice of GlobBuilder::build (glob.rs:600-631) + Glob::new
// (glob.rs:288-292): the parser drive and the branch-count epilogue.
// The `re` field of the returned Glob (glob.rs:626, the
// Tokens::to_regex_with call) mounts with this batch: the exec twin
// to_regex_with_exec above is the `re` carrier (the upstream field is
// built in the same build tail; the weld surface is GL8's diff-set).
// ===========================================================================

/// Origin Rust (glob.rs:600-631, the GL2 slice):
///     pub fn build(&self) -> Result<Glob, Error> {
///         let mut p = Parser { ... };
///         p.parse()?;
///         if p.branches.is_empty() {
///             // OK because of how the the branches/alternate_stack are
///             // managed. If we end up here, then there *must* be a bug
///             // in the parser somewhere.
///             unreachable!()
///         } else if p.branches.len() > 1 {
///             Err(Error { glob: Some(self.glob.to_string()),
///                         kind: ErrorKind::UnclosedAlternates })
///         } else {
///             let tokens = p.branches.pop().unwrap();
///             Ok(Glob { ... tokens, ... })
///         }
///     }
/// (the unreachable! site is proven dead below via parse's
///  branches >= 1 postcondition -- the upstream comment's own claim,
///  re-derived as the machine domain invariant)
pub fn glob_parse(glob: Vec<char>, opts: GlobOptions, windows: bool) -> (r: Result<Vec<Token>, GlobError>)
    requires
        glob.len() < 1073741824,
    ensures
        r is Err ==> is_parse_error(r.get_Err_0().kind),
        r is Ok ==> r.get_Ok_0()@.len() >= 0,
{
    let mut p = Parser::new(glob, opts);
    match p.parse(windows) {
        Err(e) => return Err(e),
        Ok(()) => {},
    }
    if p.branches.len() == 0 {
        // OK because of how the the branches/alternate_stack are
        // managed. If we end up here, then there *must* be a bug in the
        // parser somewhere. (glob.rs:613-616; dead per parse's post)
        assert(false);
        unreachable!()
    } else if p.branches.len() > 1 {
        Err(GlobError::error(ErrorKind::UnclosedAlternates))
    } else {
        match p.branches.pop() {
            Some(tokens) => Ok(tokens),
            None => {
                assert(false);
                unreachable!()
            },
        }
    }
}


// ===========================================================================
// GL4 -- the strategy-extractor face (glob.rs:13-72 + 344-589).
//
// The value model: pure token-slice analyses over Seq<TokenS>, mounted
// on the GL2 parse machine (spec_parse_glob) exactly the way upstream
// mounts the extractors on Glob::tokens. The classification twin
// (spec_match_strategy) carries the MatchStrategy::new precedence
// order verbatim (glob.rs:52-71):
//     BasenameLiteral > Literal > Extension > Prefix > Suffix >
//     RequiredExtension > BasenameRegex > Regex.
// The KAT ride: the 46 extract!-family fixtures (glob.rs:1649-1719)
// plus the XV boundary set; the truth table is the two-tree run
// (out/kverus-run/GL4, oracle = the pinned upstream copy vs mirror =
// the plain-Rust twin of this spec family).
//
// Walk idiom note (the #GL-9 line of jurisprudence, extended): the
// collector/gate recursions are written in the fuel + subrange-tail
// form that by(compute) folds (probe_units/p_min4 vs p_min1/p_min3:
// the i/nat-stepped variants spin the compute fallback indefinitely
// -- a new #GL-10 entry in the batch ledger). Fuel semantics: entry
// sites pass ts.len() (collector walks never need more), truncation
// returns the refusal values (None for the collectors, false for the
// bool gate) -- a truncated walk never certifies a partial
// collection, so every Some/true the family returns is a full one.
//
// GM charter anchors quoted per site: GM11 (required_ext: necessary
// but NOT sufficient), GM12 (suffix component: the leading-'/'
// guarantee), GM13 (basename_tokens: None when any basename match
// could fall outside the whole-pattern match) -- the statable halves
// predicate-erected below (lemma_basename_tokens_gate,
// lemma_suffix_entire_leads_slash); the path-correspondence halves
// are the GL5 weld obligation (recorded in the batch notes).
// ===========================================================================

/// Origin Rust (glob.rs:339-351):
///     /// Returns the pattern as a literal if and only if the pattern
///     /// must match an entire path exactly.
///     ///
///     /// The basic format of these patterns is `{literal}`.
///     fn literal(&self) -> Option<String> {
///         if self.opts.case_insensitive { return None; }
///         let mut lit = String::new();
///         for t in &*self.tokens {
///             let Token::Literal(c) = *t else { return None };
///             lit.push(c);
///         }
///         if lit.is_empty() { None } else { Some(lit) }
///     }
pub open spec fn spec_literal(opts: GlobOptions, ts: Seq<TokenS>) -> Option<Seq<char>> {
    if opts.case_insensitive {
        None
    } else {
        spec_lit_walk(ts, Seq::empty(), ts.len())
    }
}

/// The literal collector walk (the `for t in &*self.tokens` loop of
/// glob.rs:345-348: all-Literal or None, then the is_empty refuser).
/// Tail-consuming, fuel-driven; fuel-0 truncation refuses (None), so
/// every Some is a complete collection.
pub open spec fn spec_lit_walk(ts: Seq<TokenS>, acc: Seq<char>, fuel: nat) -> Option<Seq<char>>
    decreases fuel
{
    if ts.len() == 0 || fuel == 0 {
        if acc.len() == 0 {
            None
        } else {
            Some(acc)
        }
    } else {
        match ts.index(0) {
            TokenS::Lit(c) => spec_lit_walk(ts.subrange(1, ts.len() as int), acc.push(c), (fuel - 1) as nat),
            _ => None,
        }
    }
}

/// Origin Rust (glob.rs:352-387):
///     /// Returns an extension if this pattern matches a file path if
///     /// and only if the file path has the extension returned.
///     /// (GM9 doc body: the extension includes the '.'; paths like
///     /// `.rs` are considered to have an extension of `.rs`.)
///     fn ext(&self) -> Option<String> {
///         if self.opts.case_insensitive { return None; }
///         let start = match *self.tokens.get(0)? {
///             Token::RecursivePrefix => 1,
///             _ => 0,
///         };
///         match *self.tokens.get(start)? {
///             Token::ZeroOrMore => {
///                 // If there was no recursive prefix, then we only
///                 // permit `*` if `*` can match a `/`. For example, if
///                 // `*` can't match `/`, then `*.c` doesn't match
///                 // `foo/bar.c`.
///                 if start == 0 && self.opts.literal_separator {
///                     return None;
///                 }
///             }
///             _ => return None,
///         }
///         match *self.tokens.get(start + 1)? {
///             Token::Literal('.') => {}
///             _ => return None,
///         }
///         let mut lit = ".".to_string();
///         for t in self.tokens[start + 2..].iter() {
///             match *t {
///                 Token::Literal('.') | Token::Literal('/') => return None,
///                 Token::Literal(c) => lit.push(c),
///                 _ => return None,
///             }
///         }
///         if lit.is_empty() { None } else { Some(lit) }
///     }
/// (the `?` on tokens.get(0) ALSO rejects the empty pattern -- the
///  length guards below carry that column; the is_empty refuser is
///  dead here (the '.' seed) but transcribed faithfully).
pub open spec fn spec_ext(opts: GlobOptions, ts: Seq<TokenS>) -> Option<Seq<char>> {
    if opts.case_insensitive {
        None
    } else {
        let start = if ts.len() > 0 && (ts.index(0) is RecP) {
            1nat
        } else {
            0nat
        };
        if ts.len() <= start {
            // glob.rs:367: `*self.tokens.get(start)?` -- empty or short
            // (a lone RecP head with nothing behind it).
            None
        } else if !(ts.index(start as int) is Zom) {
            None
        } else if start == 0 && opts.literal_separator {
            // glob.rs:373-375: if `*` can't match `/`, then `*.c`
            // doesn't match `foo/bar.c`.
            None
        } else if ts.len() < start + 2 {
            // glob.rs:379: `*self.tokens.get(start + 1)?`
            None
        } else if ts.index((start + 1) as int) != TokenS::Lit('.') {
            None
        } else {
            spec_ext_walk(ts.subrange((start + 2) as int, ts.len() as int), seq!['.'], ts.len())
        }
    }
}

/// The extension body walk (glob.rs:381-386: the '.'/'/' refusers and
/// the Literal collector over tokens[start+2..]).
pub open spec fn spec_ext_walk(ts: Seq<TokenS>, acc: Seq<char>, fuel: nat) -> Option<Seq<char>>
    decreases fuel
{
    if ts.len() == 0 || fuel == 0 {
        if acc.len() == 0 {
            None
        } else {
            Some(acc)
        }
    } else {
        match ts.index(0) {
            TokenS::Lit('.') | TokenS::Lit('/') => None,
            TokenS::Lit(c) => spec_ext_walk(ts.subrange(1, ts.len() as int), acc.push(c), (fuel - 1) as nat),
            _ => None,
        }
    }
}

/// Origin Rust (glob.rs:392-419):
///     /// This is like `ext`, but returns an extension even if it
///     /// isn't sufficient to imply a match. Namely, if an extension
///     /// is returned, then it is necessary but not sufficient for a
///     /// match.
///     fn required_ext(&self) -> Option<String> {
///         if self.opts.case_insensitive { return None; }
///         // We don't care at all about the beginning of this
///         // pattern. All we need to check for is if it ends with a
///         // literal of the form `.ext`.
///         let mut ext: Vec<char> = vec![]; // built in reverse
///         for t in self.tokens.iter().rev() {
///             match *t {
///                 Token::Literal('/') => return None,
///                 Token::Literal(c) => {
///                     ext.push(c);
///                     if c == '.' { break; }
///                 }
///                 _ => return None,
///             }
///         }
///         if ext.last() != Some(&'.') { None } else {
///             ext.reverse(); Some(ext.into_iter().collect())
///         }
///     }
/// (GM11's charter -- "A pattern matches only if the given extension
///  matches ... necessary but NOT sufficient ... a full regex search
///  is still required" (the variant doc, glob.rs:37-40) -- is a
///  STRATEGY-TIER property: its false-positive freedom is the GL5
///  weld obligation; GL4 carries the rev-scan value exactly.)
/// Fuel semantics: the reverse scan truncates by refusing (None).
/// The value model of push-then-reverse is the head-cons accumulator
/// (front); the loop-exhaust column reduces to None because an
/// exhausted walk's top-of-stack char is never the break dot (the
/// only '.' that could top it is one the loop broke on).
pub open spec fn spec_required_ext(opts: GlobOptions, ts: Seq<TokenS>) -> Option<Seq<char>> {
    if opts.case_insensitive {
        None
    } else {
        spec_req_ext_walk(ts, ts.len() as int - 1, Seq::empty(), ts.len())
    }
}

/// The reverse scan (glob.rs:407-417): '/' anywhere in the tail kills
/// it, any non-Literal kills it, the first '.' from the right stops
/// the scan and returns the collected head.
pub open spec fn spec_req_ext_walk(
    ts: Seq<TokenS>,
    i: int,
    front: Seq<char>,
    fuel: nat,
) -> Option<Seq<char>>
    decreases fuel
{
    if fuel == 0 {
        // truncated: never certify a partial head
        None
    } else if i < 0 {
        // glob.rs:417-419: loop exhausted -- ext.last() != Some(&'.').
        None
    } else {
        match ts.index(i) {
            TokenS::Lit('/') => None,
            TokenS::Lit(c) => {
                if c == '.' {
                    Some(seq!['.'] + front)
                } else {
                    spec_req_ext_walk(
                        ts,
                        i - 1,
                        seq![c] + front,
                        (fuel - 1) as nat,
                    )
                }
            },
            _ => None,
        }
    }
}

/// Origin Rust (glob.rs:421-451):
///     /// Returns a literal prefix of this pattern if the entire
///     /// pattern matches if the literal prefix matches.
///     fn prefix(&self) -> Option<String> {
///         if self.opts.case_insensitive { return None; }
///         let (end, need_sep) = match *self.tokens.last()? {
///             Token::ZeroOrMore => {
///                 if self.opts.literal_separator {
///                     // If a trailing `*` can't match a `/`, then we
///                     // can't assume a match of the prefix corresponds
///                     // to a match of the overall pattern. e.g.,
///                     // `foo/*` with `literal_separator` enabled
///                     // matches `foo/bar` but not `foo/bar/baz`, even
///                     // though `foo/bar/baz` has a `foo/` literal
///                     // prefix.
///                     return None;
///                 }
///                 (self.tokens.len() - 1, false)
///             }
///             Token::RecursiveSuffix => (self.tokens.len() - 1, true),
///             _ => (self.tokens.len(), false),
///         };
///         let mut lit = String::new();
///         for t in &self.tokens[0..end] {
///             let Token::Literal(c) = *t else { return None };
///             lit.push(c);
///         }
///         if need_sep { lit.push('/'); }
///         if lit.is_empty() { None } else { Some(lit) }
///     }
/// (the trailing-star Zom walk skews the `[^/]*` star so the prefix
///  stays sound for path-crossing `*`s; the literal '/' token before
///  the star rides the walk itself -- the `/foo/*` KAT's tokenization
///  is [.., Lit('/'), Zom], so the collected prefix carries the
///  trailing '/'; pinned by extract_prefix2.)
pub open spec fn spec_prefix(opts: GlobOptions, ts: Seq<TokenS>) -> Option<Seq<char>> {
    if opts.case_insensitive {
        None
    } else {
        if ts.len() == 0 {
            None // glob.rs:433: `*self.tokens.last()?`
        } else {
            let last = ts.index(ts.len() - 1);
            if last is Zom {
                if opts.literal_separator {
                    None
                } else {
                    spec_prefix_walk(ts, (ts.len() - 1) as int, Seq::empty(), false, ts.len())
                }
            } else if last is RecS {
                spec_prefix_walk(ts, (ts.len() - 1) as int, Seq::empty(), true, ts.len())
            } else {
                spec_prefix_walk(ts, ts.len() as int, Seq::empty(), false, ts.len())
            }
        }
    }
}

/// The bounded literal walk (glob.rs:443-451 over tokens[0..end],
/// then the need_sep '/' append and the is_empty refuser). `remaining`
/// counts the still-unvisited window (the value model of range end).
pub open spec fn spec_prefix_walk(
    ts: Seq<TokenS>,
    remaining: int,
    acc: Seq<char>,
    need_sep: bool,
    fuel: nat,
) -> Option<Seq<char>>
    decreases fuel
{
    if remaining <= 0 || fuel == 0 {
        let lit = if need_sep {
            acc + seq!['/']
        } else {
            acc
        };
        if lit.len() == 0 {
            None
        } else {
            Some(lit)
        }
    } else if ts.len() == 0 {
        // no more tokens though the window claims some (never reached
        // from the entry windows; total-value shaping)
        None
    } else {
        match ts.index(0) {
            TokenS::Lit(c) => spec_prefix_walk(
                ts.subrange(1, ts.len() as int),
                remaining - 1,
                acc.push(c),
                need_sep,
                (fuel - 1) as nat,
            ),
            _ => None,
        }
    }
}

/// Origin Rust (glob.rs:453-502):
///     /// Returns a literal suffix of this pattern if the entire
///     /// pattern matches if the literal suffix matches.
///     ///
///     /// If a literal suffix is returned and it must match either the
///     /// entire file path or be preceded by a `/`, then also return
///     /// true. This happens with a pattern like `**/foo/bar`. Namely,
///     /// this pattern matches `foo/bar` and `baz/foo/bar`, but not
///     /// `foofoo/bar`. In this case, the suffix returned is
///     /// `/foo/bar` (but should match the entire path `foo/bar`).
///     ///
///     /// When this returns true, the suffix literal is guaranteed to
///     /// start with a `/`.
///     fn suffix(&self) -> Option<(String, bool)> {
///         if self.opts.case_insensitive { return None; }
///         let mut lit = String::new();
///         let (start, entire) = match *self.tokens.get(0)? {
///             Token::RecursivePrefix => {
///                 // We only care if this follows a path component if
///                 // the next token is a literal.
///                 if let Some(&Token::Literal(_)) = self.tokens.get(1) {
///                     lit.push('/'); (1, true)
///                 } else { (1, false) }
///             }
///             _ => (0, false),
///         };
///         let start = match *self.tokens.get(start)? {
///             Token::ZeroOrMore => {
///                 // If literal_separator is enabled, then a `*` can't
///                 // necessarily match everything, so reporting a
///                 // suffix match as a match of the pattern would be
///                 // a false positive.
///                 if self.opts.literal_separator { return None; }
///                 start + 1
///             }
///             _ => start,
///         };
///         for t in &self.tokens[start..] {
///             let Token::Literal(c) = *t else { return None };
///             lit.push(c);
///         }
///         if lit.is_empty() || lit == "/" { None } else { Some((lit, entire)) }
///     }
/// (GM12's charter is the quoted closing doc line: "When this returns
///  true, the suffix literal is guaranteed to start with a `/`" --
///  PREDICATE-ERECTED at lemma_suffix_entire_leads_slash below, the
///  GL4-side half; the lib.rs:497-501 consumer strip is GL7.)
pub open spec fn spec_suffix_launch(ts: Seq<TokenS>) -> (nat, Seq<char>, bool) {
    let head_rec = ts.len() > 0 && (ts.index(0) is RecP);
    let next_is_lit = ts.len() > 1 && (ts.index(1) is Lit);
    if head_rec && next_is_lit {
        // glob.rs:487-489: we only care if this follows a path
        // component if the next token is a literal.
        (1nat, seq!['/'], true)
    } else if head_rec {
        (1nat, Seq::empty(), false)
    } else {
        (0nat, Seq::empty(), false)
    }
}

pub open spec fn spec_suffix(opts: GlobOptions, ts: Seq<TokenS>) -> Option<(Seq<char>, bool)> {
    if opts.case_insensitive {
        None
    } else if ts.len() == 0 {
        None // glob.rs:483: `*self.tokens.get(0)?`
    } else {
        let (start0, pre, entire) = spec_suffix_launch(ts);
        // glob.rs:494-502: the Zom skip and its literal_separator
        // false-positive refusal.
        let at_zom = ts.len() as int > start0 as int && (ts.index(start0 as int) is Zom);
        if at_zom && opts.literal_separator {
            None
        } else {
            let start1 = if at_zom {
                (start0 + 1) as nat
            } else {
                start0
            };
            let walked = spec_suffix_walk(ts.subrange(start1 as int, ts.len() as int), pre, ts.len());
            if walked is None {
                None
            } else {
                Some((walked.get_Some_0(), entire))
            }
        }
    }
}

/// The suffix body walk (glob.rs:503-506) + the is_empty / lone-'/'
/// refusers of glob.rs:507. The `entire` flag does not ride the walk
/// (upstream passes it through constant): the value model splices it
/// back at the spec_suffix call site (a pure refactor -- equal values
/// on every input); truncation refuses (None).
pub open spec fn spec_suffix_walk(
    ts: Seq<TokenS>,
    pre: Seq<char>,
    fuel: nat,
) -> Option<Seq<char>>
    decreases fuel
{
    if ts.len() == 0 || fuel == 0 {
        if pre.len() == 0 || pre == seq!['/'] {
            None
        } else {
            Some(pre)
        }
    } else {
        match ts.index(0) {
            TokenS::Lit(c) => spec_suffix_walk(ts.subrange(1, ts.len() as int), pre.push(c), (fuel - 1) as nat),
            _ => None,
        }
    }
}

/// Origin Rust (glob.rs:508-551):
///     /// If this pattern only needs to inspect the basename of a
///     /// file path, then the tokens corresponding to only the
///     /// basename match are returned.
///     ///
///     /// For example, given a pattern of `**/*.foo`, only the tokens
///     /// corresponding to `*.foo` are returned.
///     ///
///     /// Note that this will return None if any match of the basename
///     /// tokens doesn't correspond to a match of the entire pattern.
///     /// For example, the glob `foo` only matches when a file path
///     /// has a basename of `foo`, but doesn't *always* match when a
///     /// file path has a basename of `foo`. e.g., `foo` doesn't
///     /// match `abc/foo`.
///     fn basename_tokens(&self) -> Option<&[Token]> {
///         let start = match *self.tokens.get(0)? {
///             Token::RecursivePrefix => 1,
///             _ => {
///                 // With nothing to gobble up the parent portion of
///                 // a path, we can't assume that matching on only
///                 // the basename is correct.
///                 return None;
///             }
///         };
///         if self.tokens[start..].is_empty() { return None; }
///         for t in self.tokens[start..].iter() {
///             match *t {
///                 Token::Literal('/') => return None,
///                 Token::Literal(_) => {} // OK
///                 Token::Any | Token::ZeroOrMore => {
///                     if !self.opts.literal_separator {
///                         // In this case, `*` and `?` can match a
///                         // path separator, which means this could
///                         // reach outside the basename.
///                         return None;
///                     }
///                 }
///                 Token::RecursivePrefix
///                 | Token::RecursiveSuffix
///                 | Token::RecursiveZeroOrMore => { return None; }
///                 Token::Class { negated, ref ranges } => {
///                     let contains_slash = ranges.iter().any(
///                         |&(start, end)| start <= '/' && '/' <= end);
///                     if contains_slash != negated { return None; }
///                 }
///                 Token::Alternates(..) => { return None; }
///             }
///         }
///         Some(&self.tokens[start..])
///     }
/// (GM13's charter is the quoted doc line "this will return None if
///  any match of the basename tokens doesn't correspond to a match of
///  the entire pattern": the PATH-CORRESPONDENCE half needs the
///  token-model semantics relation (the GL3-registered GL5 input
///  face) and is registered there; the CLAUSE half is what GL4 can
///  and does predicate-erect -- lemma_basename_tokens_gate below
///  pins that every returned slice element is gate-clean per this
///  exact decision table, which is precisely the premise set the GL5
///  weld consumes.)
pub open spec fn spec_basename_tokens(opts: GlobOptions, ts: Seq<TokenS>) -> Option<Seq<TokenS>> {
    if ts.len() == 0 || !(ts.index(0) is RecP) {
        // glob.rs:511-530: with nothing to gobble up the parent
        // portion of a path, we can't assume that matching on only
        // the basename is correct.
        None
    } else if ts.len() == 1 {
        // glob.rs:533-535: the empty tail refuser.
        None
    } else if spec_basename_gate_scan(opts, ts, 1, 1, ts.len()) {
        Some(ts.subrange(1, ts.len() as int))
    } else {
        None
    }
}

/// The per-token gate decision table (glob.rs:537-556, one clause per
/// arm, spelled as a predicate so the GL5 weld consumes it directly):
/// the '/' literal refuser, the Any/Zom literal_separator demand, the
/// recursive refusers, the Class contains_slash/!=negated gate, and
/// the alternates refuser.
pub open spec fn spec_basename_token_ok(opts: GlobOptions, t: TokenS) -> bool {
    match t {
        TokenS::Lit('/') => false,
        TokenS::Lit(_) => true,
        TokenS::Any | TokenS::Zom => {
            // In this case, `*` and `?` can match a path separator,
            // which means this could reach outside the basename.
            opts.literal_separator
        },
        TokenS::RecP | TokenS::RecS | TokenS::RecZ => false,
        TokenS::Cls { negated, ranges } => {
            // glob.rs:554-557: a plain class may not cover '/', a
            // negated class must cover it (both keep '/' out of the
            // basename reach).
            spec_ranges_contain_slash(ranges) == negated
        },
        TokenS::Alts(_) => false,
    }
}

/// The gate sweep (the for-loop of glob.rs:536-556): scan true iff
/// every token from start on passes the per-token gate. The start
/// parameter threads the RecP offset (always 1 here; kept explicit so
/// the induction mirrors the upstream loop); truncation refuses
/// (false), so a true verdict is always a complete sweep -- the entry
/// passes ts.len() and never truncates.
pub open spec fn spec_basename_gate_scan(
    opts: GlobOptions,
    ts: Seq<TokenS>,
    start: nat,
    done: nat,
    fuel: nat,
) -> bool
    decreases fuel
{
    if done as int >= ts.len() as int {
        true
    } else if fuel == 0 {
        // truncated: never certify a partial sweep
        false
    } else {
        spec_basename_token_ok(opts, ts.index(done as int))
            && spec_basename_gate_scan(opts, ts, start, (done + 1) as nat, (fuel - 1) as nat)
    }
}

/// The contains_slash column (glob.rs:554-556's ranges.iter().any()):
/// some range (start, end) with start <= '/' <= end. Fuel-driven tail
/// consumption; truncation = false (no partial certification).
pub open spec fn spec_ranges_contain_slash(rs: Seq<(char, char)>) -> bool {
    spec_ranges_slash_upto(rs, rs.len())
}

/// The sweep over the last `fuel`-window of the range list (the any()
/// column as a backward accumulation over an index budget).
pub open spec fn spec_ranges_slash_upto(rs: Seq<(char, char)>, up_to: nat) -> bool
    decreases up_to
{
    if up_to == 0 {
        false
    } else {
        let r = rs.index((up_to - 1) as int);
        (r.0 <= '/' && '/' <= r.1) || spec_ranges_slash_upto(rs, (up_to - 1) as nat)
    }
}

/// Origin Rust (glob.rs:567-578):
///     /// Returns the pattern as a literal if and only if the pattern
///     /// exclusively matches the basename of a file path *and* is a
///     /// literal.
///     ///
///     /// The basic format of these patterns is `**/{literal}`, where
///     /// `{literal}` does not contain a path separator.
///     fn basename_literal(&self) -> Option<String> {
///         if self.opts.case_insensitive { return None; }
///         let tokens = self.basename_tokens()?;
///         let mut lit = String::new();
///         for t in tokens {
///             let Token::Literal(c) = *t else { return None };
///             lit.push(c);
///         }
///         Some(lit)
///     }
/// (no is_empty refuser upstream -- transcribed as-is: the gate's
///  nonempty-tail demand carries the emptiness column.)
pub open spec fn spec_basename_literal(opts: GlobOptions, ts: Seq<TokenS>) -> Option<Seq<char>> {
    if opts.case_insensitive {
        None
    } else {
        match spec_basename_tokens(opts, ts) {
            None => None,
            Some(bs) => spec_basename_literal_walk(bs, Seq::empty(), bs.len()),
        }
    }
}

pub open spec fn spec_basename_literal_walk(
    ts: Seq<TokenS>,
    acc: Seq<char>,
    fuel: nat,
) -> Option<Seq<char>>
    decreases fuel
{
    if ts.len() == 0 || fuel == 0 {
        Some(acc)
    } else {
        match ts.index(0) {
            TokenS::Lit(c) => spec_basename_literal_walk(
                ts.subrange(1, ts.len() as int),
                acc.push(c),
                (fuel - 1) as nat,
            ),
            _ => None,
        }
    }
}

/// Origin Rust (glob.rs:580-589):
///     /// Returns a regex for the basename when it determines the
///     /// whole match.
///     fn basename_regex(&self) -> Option<String> {
///         let tokens = self.basename_tokens()?;
///         Some(Tokens::to_regex_with(&self.opts, tokens))
///     }
/// (no case_insensitive early-out upstream -- the CASEI column of a
///  `**/literal` pattern therefore classifies BasenameRegex with the
///  (?i) prologue, NOT nothing; pinned by xv_casei_base and
///  extract_basetoks2 in the KAT and the two-tree run. The fuel rides
///  through to the GL3 emission twin (spec_to_regex_with).)
pub open spec fn spec_basename_regex(opts: GlobOptions, ts: Seq<TokenS>, fuel: nat) -> Option<Seq<char>> {
    match spec_basename_tokens(opts, ts) {
        None => None,
        Some(bs) => Some(spec_to_regex_with(opts, bs, fuel)),
    }
}

/// Origin Rust (glob.rs:13-46, the enum + variant docs):
///     /// Describes a matching strategy for a particular pattern.
///     /// (.. "A pattern matches if and only if .." per variant ..)
///     pub(crate) enum MatchStrategy {
///         Literal(String),
///         BasenameLiteral(String),
///         Extension(String),
///         Prefix(String),
///         Suffix { suffix: String, component: bool },
///         RequiredExtension(String),
///         BasenameRegex(String),
///         Regex,
///     }
/// The Seq<char> twin of the payloads; the Suffix.component doc
/// ("An exception: if `component` is true, then `suffix` must appear
///  at the beginning of a file path or immediately following a `/`")
/// is the twin's GM12-side semantics carrier.
pub enum MatchStrategyS {
    Literal(Seq<char>),
    BasenameLiteral(Seq<char>),
    Extension(Seq<char>),
    Prefix(Seq<char>),
    Suffix {
        suffix: Seq<char>,
        component: bool,
    },
    RequiredExtension(Seq<char>),
    BasenameRegex(Seq<char>),
    Regex,
}

/// Origin Rust (glob.rs:50-72, MatchStrategy::new -- the
/// classification precedence, arms in upstream order):
///     pub(crate) fn new(pat: &Glob) -> MatchStrategy {
///         if let Some(lit) = pat.basename_literal() {
///             MatchStrategy::BasenameLiteral(lit)
///         } else if let Some(lit) = pat.literal() {
///             MatchStrategy::Literal(lit)
///         } else if let Some(ext) = pat.ext() {
///             MatchStrategy::Extension(ext)
///         } else if let Some(prefix) = pat.prefix() {
///             MatchStrategy::Prefix(prefix)
///         } else if let Some((suffix, component)) = pat.suffix() {
///             MatchStrategy::Suffix { suffix, component }
///         } else if let Some(ext) = pat.required_ext() {
///             MatchStrategy::RequiredExtension(ext)
///         } else if let Some(re) = pat.basename_regex() {
///             MatchStrategy::BasenameRegex(re)
///         } else {
///             MatchStrategy::Regex
///         }
///     }
pub open spec fn spec_match_strategy(opts: GlobOptions, ts: Seq<TokenS>, fuel: nat) -> MatchStrategyS {
    match spec_basename_literal(opts, ts) {
        Some(lit) => MatchStrategyS::BasenameLiteral(lit),
        None => match spec_literal(opts, ts) {
            Some(lit) => MatchStrategyS::Literal(lit),
            None => match spec_ext(opts, ts) {
                Some(ext) => MatchStrategyS::Extension(ext),
                None => match spec_prefix(opts, ts) {
                    Some(pre) => MatchStrategyS::Prefix(pre),
                    None => match spec_suffix(opts, ts) {
                        Some((suffix, component)) => MatchStrategyS::Suffix { suffix, component },
                        None => match spec_required_ext(opts, ts) {
                            Some(ext) => MatchStrategyS::RequiredExtension(ext),
                            None => match spec_basename_regex(opts, ts, fuel) {
                                Some(re) => MatchStrategyS::BasenameRegex(re),
                                None => MatchStrategyS::Regex,
                            },
                        },
                    },
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// GL4 lemma family -- the predication half of the GM charters that is
// statable INSIDE this batch (the path-correspondence halves are GL5
// weld material; both boundaries are recorded in the batch notes).
// ---------------------------------------------------------------------------

/// Sub-lemma: a passing gate scan certifies every element from the
/// scan point on. Induction on fuel (the scan's own recursion
/// supplies the tail, the definitional step the head, the empty range
/// at done == ts.len() and the truncation-refusal at fuel == 0 the
/// vacuous bases).
pub proof fn lemma_gate_scan_true_implies_all(
    opts: GlobOptions,
    ts: Seq<TokenS>,
    start: nat,
    done: nat,
    fuel: nat,
)
    requires
        start as int <= done as int <= ts.len() as int,
    ensures
        spec_basename_gate_scan(opts, ts, start, done, fuel) ==> (forall|j: int|
            done as int <= j < ts.len() as int ==> spec_basename_token_ok(opts, ts.index(j))),
    decreases fuel
{
    if done as int >= ts.len() as int {
        // the tail range [done, ts.len()) is empty: vacuous base.
    } else if fuel == 0 {
        // truncation refusal: scan is false, implication vacuous.
    } else {
        let rest = spec_basename_gate_scan(opts, ts, start, (done + 1) as nat, (fuel - 1) as nat);
        // The definitional step: scan(start, done, fuel) =
        // ok(ts[done]) && scan(start, done + 1, fuel - 1).
        assert(spec_basename_gate_scan(opts, ts, start, done, fuel)
            == (spec_basename_token_ok(opts, ts.index(done as int)) && rest));
        // The tail certification.
        lemma_gate_scan_true_implies_all(opts, ts, start, (done + 1) as nat, (fuel - 1) as nat);
        // Combine under the scan hypothesis: the head from the
        // definitional step, the tail from the callee's ensures.
        if spec_basename_gate_scan(opts, ts, start, done, fuel) {
            assert(spec_basename_token_ok(opts, ts.index(done as int)));
            assert(rest);
            assert forall|j: int|
                done as int <= j < ts.len() as int implies spec_basename_token_ok(
                opts,
                ts.index(j),
            ) by {
                if j == done as int {
                    assert(spec_basename_token_ok(opts, ts.index(done as int)));
                } else {
                    assert(j >= (done + 1) as int);
                }
            }
        }
    }
}

/// GM13's clause-half predication (the statable half, pinned): when
/// basename_tokens returns Some, the returned slice is (a) nonempty,
/// (b) exactly the post-RecP tail slice of the pattern, and (c)
/// every token of that tail passes the per-token gate decision table
/// (the '/'-literal, Any/Zom-lit-sep, recursive, Class
/// contains_slash==negated, and alternates clauses). These are
/// precisely the premises the GL5 weld consumes. The doc's
/// path-correspondence half ("if any match of the basename tokens
/// doesn't correspond to a match of the entire pattern") needs the
/// token-model semantics relation and stays the GL5 obligation.
pub proof fn lemma_basename_tokens_gate(opts: GlobOptions, ts: Seq<TokenS>)
    ensures
        match spec_basename_tokens(opts, ts) {
            Some(sub) => sub.len() >= 1
                && sub == ts.subrange(1, ts.len() as int)
                && (forall|j: int|
                    1 <= j < ts.len() as int ==> spec_basename_token_ok(opts, ts.index(j))),
            None => true,
        },
{
    if ts.len() >= 2 && (ts.index(0) is RecP) {
        // slice length (the vstd subrange-length lemma)
        vstd::seq::lemma_seq_subrange_len(ts, 1, ts.len() as int);
        assert(ts.subrange(1, ts.len() as int).len() == ts.len() as int - 1);
        // the gate certification over the tail range (the lemma is
        // fuel-quantified; instantiate at the entry's own budget)
        lemma_gate_scan_true_implies_all(opts, ts, 1nat, 1nat, ts.len());
        if spec_basename_gate_scan(opts, ts, 1, 1, ts.len()) {
            assert(spec_basename_tokens(opts, ts) == Some(ts.subrange(1, ts.len() as int)));
        } else {
            assert(spec_basename_tokens(opts, ts) is None);
        }
    } else {
        assert(spec_basename_tokens(opts, ts) is None);
    }
}

/// GM12's predicate (the statable half, pinned): every suffix the
/// extractor pairs with component=true begins with '/' (the doc's
/// "When this returns true, the suffix literal is guaranteed to start
/// with a `/`" -- the leading '/' is exactly the RecursivePrefix-head
/// push of glob.rs:488, and the walk only ever appends after it). The
/// path-boundary CONSUMER semantics (lib.rs:497-501's strip into the
/// literal map) is the GL7 mount.
pub proof fn lemma_suffix_entire_leads_slash(opts: GlobOptions, ts: Seq<TokenS>)
    ensures
        match spec_suffix(opts, ts) {
            Some(p) => !p.1 || (p.0.len() >= 1 && p.0.index(0) == '/'),
            None => true,
        },
{
    if spec_suffix(opts, ts) is Some {
        let pair = spec_suffix(opts, ts).get_Some_0();
        if pair.1 {
            // the launch ite-chain read backwards: only its first
            // branch pairs a '/' seed with entire=true, and the very
            // branch condition (a Lit next token) blocks the Zom skip
            // for this same index -- so the launched walk is the
            // start=1 '/'-seeded one.
            let (start0, pre, launch_entire) = spec_suffix_launch(ts);
            assert(launch_entire);
            assert(start0 == 1nat);
            assert(pre == seq!['/']);
            assert(ts.len() as int > 1 && (ts.index(1) is Lit));
            assert(!(ts.index(1) is Zom));
            let at_zom = ts.len() as int > start0 as int && (ts.index(start0 as int) is Zom);
            assert(!at_zom);
            assert(spec_suffix(opts, ts).get_Some_0().0
                == spec_suffix_walk(ts.subrange(1, ts.len() as int), seq!['/'], ts.len()).get_Some_0());
            lemma_suffix_walk_head(ts.subrange(1, ts.len() as int), seq!['/'], ts.len(), true);
        }
    }
}

/// Walk shape helper: the walk's result lit has pre as a prefix, so a
/// nonempty seed keeps its head at lit[0] (Seq push preserves both
/// length >= and the index-0 slot).
pub proof fn lemma_suffix_walk_head(
    ts: Seq<TokenS>,
    pre: Seq<char>,
    fuel: nat,
    entire: bool,
)
    requires
        entire ==> (pre.len() >= 1 && pre.index(0) == '/'),
    ensures
        match (spec_suffix_walk(ts, pre, fuel), entire) {
            (Some(lit), true) => lit.len() >= 1 && lit.index(0) == '/',
            _ => true,
        },
    decreases fuel
{
    if ts.len() == 0 || fuel == 0 {
        // the base case: lit == pre, so the seed IS the head
    } else {
        match ts.index(0) {
            TokenS::Lit(c) => {
                // push keeps pre's head at index 0 and its length >= 1
                lemma_suffix_walk_head(ts.subrange(1, ts.len() as int), pre.push(c), (fuel - 1) as nat, entire);
            },
            _ => {
                // the refuser arms: no output at all
            },
        }
    }
}

// ===========================================================================
// GL5 -- the strategic-model soundness weld: the recursive token-model
// matcher (the value semantics of the GL3 emission, restated over
// chars per the D1 charter), the Candidate char-twin faces, and the
// cfg(test) GlobStrategic check promoted to a verified model.
//
// Semantics charter (Origin lib.rs:1131-1133 -- every GlobMatcher in
// this crate compiles through the same face):
///     fn new_regex(pat: &str) -> Result<Regex, Error> {
///         let syntax = regex_automata::util::syntax::Config::new()
///             .utf8(false)
///             .dot_matches_new_line(true);
/// ...
// i.e. the `.` of the emitted byte regex MATCHES newlines -- the Any /
// ZeroOrMore / Recursive* wildcard arms below therefore exclude only
// the path separator (and only under literal_separator); there is no
// '\n' exclusion anywhere in the model (the lib.rs:70-73 Syntax doc
// bullet "`?` matches any single character. (If the literal_separator
// option is enabled, then `?` can never match a path separator.)" --
// quoted sentence-by-sentence below -- is the char-side carrier).
// The char domain is the valid-UTF-8 projection: a wildcard consumes
// one WHOLE char (the byte regex consumes one byte; the two differ
// exactly on non-ASCII chars riding a wildcard -- the divergence pair
// is registered in the GL5 notes suspects table, not papered over
// here). Class membership is char-range membership likewise (the
// non-ASCII-class byte-tangle is the second registered divergence
// axis).
// ===========================================================================

/// ASCII case-fold (regex-syntax's (?-u)(?i) byte folding is ASCII
/// upper/lowercase only): 'A'..'Z' -> their lower-case counterparts,
/// everything else fixed.
pub open spec fn spec_char_low(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        // ASCII +32 lane (std's to_ascii_lowercase table, the (?i)
        // folding's only lane over the byte domain); the guard makes
        // from_u32's option always Some
        // u8->char cast (ASCII lane; the guard pins the value in 97..=122)
        (((c as u32) + 32) as u8) as char
    } else {
        c
    }
}

/// The (?i) equality edge: raw equality, or equality after the ASCII
/// fold (applied to at least one side; the fold is an involution on
/// the ASCII lanes so one side suffices).
pub open spec fn spec_fold_eq(opts: GlobOptions, c: char, d: char) -> bool {
    c == d || (opts.case_insensitive && spec_char_low(c) == spec_char_low(d))
}

/// The class-hit column (glob.rs:766-783 emission: `[` ranges `]`) as a
/// membership decision over one char: true iff c lies inside some
/// range pair. Tail consumption over the range list (GL4's slash-scan
/// pattern); truncation refuses.
pub open spec fn spec_cls_member(rs: Seq<(char, char)>, c: char) -> bool {
    spec_cls_member_upto(rs, c, rs.len())
}

pub open spec fn spec_cls_member_upto(rs: Seq<(char, char)>, c: char, up_to: nat) -> bool
    decreases up_to
{
    if up_to == 0 {
        false
    } else {
        let r = rs.index((up_to - 1) as int);
        (r.0 <= c && c <= r.1) || spec_cls_member_upto(rs, c, (up_to - 1) as nat)
    }
}

/// The per-char Class verdict of the token matcher (the (?i) fold
/// reaches into class membership exactly as the (?i) prologue reaches
/// the whole emitted regex): inside iff the raw char, or its ASCII
/// fold, hits when case_insensitive is on; the negated bit flips the
/// membership read.
pub open spec fn spec_cls_ok(opts: GlobOptions, negated: bool, rs: Seq<(char, char)>, c: char) -> bool
{
    let hit = spec_cls_member(rs, c)
        || (opts.case_insensitive && spec_cls_member(rs, spec_char_low(c)));
    hit != negated
}

// ---------------------------------------------------------------------------
// The emission-nonempty lattice: which Alternates branches survive the
// glob.rs:757-761 kept gate ("if !altre.is_empty() ||
// options.empty_alternates { parts.push(altre); }") and when the whole
// Alternates token emits anything at all (glob.rs:776-783: "It is
// possible to have an empty set in which case the resulting
// alternation '()' would be an error." / "if !parts.is_empty() {").
// These predicates drive the token matcher's Alts arm only.
// ---------------------------------------------------------------------------

/// One branch is kept iff its emission is nonempty, or the
/// empty_alternates option pushes it anyway.
pub open spec fn spec_alts_branch_kept(opts: GlobOptions, b: Seq<TokenS>, fuel: nat) -> bool {
    opts.empty_alternates || spec_tok_seq_emits(opts, b, fuel)
}

/// A token sequence emits a nonempty string iff it has some token that
/// emits a nonempty piece (concatenation of fragments; every non-Alts
/// piece is >= 1 char per the GL3 emission table). Tail-scan walker
/// (the exists-free shape the GL2-4 solver lane closes on); fuel
/// budgets every lattice hop, truncation refuses.
pub open spec fn spec_tok_seq_emits(opts: GlobOptions, b: Seq<TokenS>, fuel: nat) -> bool
    decreases fuel
{
    if fuel == 0 {
        false
    } else {
        // every lattice hop costs 1 fuel (seq -> scan, token, branch)
        spec_seq_emits_upto(opts, b, b.len() as nat, (fuel - 1) as nat)
    }
}

pub open spec fn spec_seq_emits_upto(
    opts: GlobOptions,
    b: Seq<TokenS>,
    up_to: nat,
    fuel: nat,
) -> bool
    decreases fuel
{
    if fuel == 0 || up_to == 0 {
        false
    } else {
        spec_tok_emits(opts, b.index((up_to - 1) as int), (fuel - 1) as nat)
            || spec_seq_emits_upto(
                opts, b, (up_to - 1) as nat, (fuel - 1) as nat,
            )
    }
}

/// The per-token emission-nonempty verdict: everything except a fully
/// dropped Alternates (all branches unkept) emits at least one char;
/// the ealtre arm keeps every branch (glob.rs:757-760), so a nonempty
/// branch list always emits there.
pub open spec fn spec_tok_emits(opts: GlobOptions, t: TokenS, fuel: nat) -> bool
    decreases fuel
{
    if fuel == 0 {
        // truncation: only the non-Alts lanes are emission-decidable
        // without descent
        match t {
            TokenS::Alts(_) => false,
            _ => true,
        }
    } else {
        match t {
            TokenS::Lit(_) | TokenS::Any | TokenS::Zom | TokenS::RecP | TokenS::RecS
            | TokenS::RecZ | TokenS::Cls { .. } => true,
            TokenS::Alts(ps) => ps.len() > 0 && spec_pats_kept_scan(
                opts, ps, ps.len() as nat, (fuel - 1) as nat,
            ),
        }
    }
}

/// The kept-scan over an Alternates branch list: some branch kept
/// (tail scan; no quantifier).
pub open spec fn spec_pats_kept_scan(
    opts: GlobOptions,
    ps: Seq<Seq<TokenS>>,
    up_to: nat,
    fuel: nat,
) -> bool
    decreases fuel
{
    if fuel == 0 || up_to == 0 {
        false
    } else {
        spec_tok_seq_emits(opts, ps.index((up_to - 1) as int), (fuel - 1) as nat)
            || spec_pats_kept_scan(
                opts, ps, (up_to - 1) as nat, (fuel - 1) as nat,
            )
    }
}

// ---------------------------------------------------------------------------
// The token-model matcher: spec_tokens_match(opts, tokens, path) is the
// value semantics of the GL3 emission -- "will represent the matching
// semantics of this glob pattern" (GM10's second half, now with a
// consumer). Anchored both ends (the '^'/'$' of to_regex_with), one
// char consumed per elementary event; the fuel parameter budgets the
// elementary events (a token step or a char step each cost 1; an Alts
// frame entry costs 1 as well). Any accepting run over ts against p
// uses at most (#nested tokens + frame hops + path.len) events, so a
// fuel of (2*nested_tokens + p.len() + 6) can never truncate one; the
// KAT harness generates exactly that per-vector budget.
// ---------------------------------------------------------------------------

/// Origin upstream (glob.rs:1163 -- Syntax doc carrier lib.rs:69-91,
/// quoted per arm in the notes):
/// * "`?` matches any single character. (If the `literal_separator`
///   option is enabled, then `?` can never match a path separator.)"
/// * "`*` matches zero or more characters. (If the `literal_separator`
///   option is enabled, then `*` can never match a path separator.)"
/// * "`**` recursively matches directories but are only legal in
///   three situations." (the three emissions: `(?:/?|.*/)`,
///   `/.*`, `(?:/|/.*/)`)
/// * "`{a,b}` matches `a` or `b` where `a` and `b` are arbitrary glob
///   patterns."
/// * "`[ab]` matches `a` or `b` where `a` and `b` are characters. Use
///   `[!ab]` to match any character except `a` and `b`."
/// The '.' flavor is newline-permissive per lib.rs:272-274
/// (dot_matches_new_line(true)); the char-level restatement is the
/// registered divergence pair's doc-side reading.
pub open spec fn spec_tokens_match(opts: GlobOptions, ts: Seq<TokenS>, p: Seq<char>, fuel: nat) -> bool {
    // Origin glob.rs:701-707 (to_regex_with special case):
    // "Special case. If the entire glob is just `**`, then it should
    //  match everything."  ([RecP] alone emits ".*", not the
    //  recursive-prefix group.)
    if ts.len() == 1 && ts.index(0) is RecP {
        spec_tm_all_chars(p, 0nat, fuel)
    } else {
        spec_tm_at(opts, ts, p, 0nat, 0nat, p.len() as nat, fuel)
    }
}

/// The anchored walk: ts[i..] matches p[j..jj). Terminal: token
/// exhaustion must coincide with the end window.
pub open spec fn spec_tm_at(
    opts: GlobOptions,
    ts: Seq<TokenS>,
    p: Seq<char>,
    i: nat,
    j: nat,
    jj: nat,
    fuel: nat,
) -> bool
    decreases fuel
{
    if i as int >= ts.len() as int {
        j as int == jj as int
    } else if fuel == 0 {
        // truncation refuses: an out-of-budget run reads false
        false
    } else {
        // the cast hoist: the verus parser refuses `x as int <` in a
        // match-arm value position (#GL-3 family grammar quirk; plain
        // identifiers in the comparisons below)
        let j_i = j as int;
        let jj_i = jj as int;
        let f1 = (fuel - 1) as nat;
        let i1 = (i + 1) as nat;
        match ts.index(i as int) {
            TokenS::Lit(c) => (j_i < jj_i)
                && spec_fold_eq(opts, c, p.index(j as int))
                && spec_tm_at(opts, ts, p, i1, (j + 1) as nat, jj, f1),
            TokenS::Any => (j_i < jj_i)
                && (!opts.literal_separator || p.index(j as int) != '/')
                && spec_tm_at(
                    opts, ts, p, i1, (j + 1) as nat, jj, f1,
                ),
            TokenS::Zom => {
                // zero chars (skip the token), or consume one more
                // (stay on the token)
                spec_tm_at(opts, ts, p, i1, j, jj, f1)
                    || ((j_i < jj_i)
                        && (!opts.literal_separator || p.index(j as int) != '/')
                        && spec_tm_at(opts, ts, p, i, (j + 1) as nat, jj, f1))
            },
            TokenS::RecP => {
                // (?:/?|.*/) -- the empty arm, or some >= 1 chars
                // whose last consumed char is '/'
                spec_tm_at(opts, ts, p, i1, j, jj, f1)
                    || spec_tm_recp_star(opts, ts, p, i, j, jj, f1)
            },
            TokenS::RecS => {
                // /.* -- a literal '/', then any number of any chars
                (j_i < jj_i)
                    && p.index(j as int) == '/'
                    && spec_tm_dot_star(opts, ts, p, i, (j + 1) as nat, jj, f1)
            },
            TokenS::RecZ => {
                // (?:/|/.*/) -- bare '/', or '/' + >= 0 chars + '/'
                (j_i < jj_i
                    && p.index(j as int) == '/'
                    && spec_tm_at(
                        opts, ts, p, i1, (j + 1) as nat, jj, f1,
                    ))
                    || (j_i < jj_i
                        && p.index(j as int) == '/'
                        && spec_tm_recz_tail(opts, ts, p, i, (j + 1) as nat, jj, f1))
            },
            TokenS::Cls { negated, ranges } => (j_i < jj_i)
                && spec_cls_ok(opts, negated, ranges, p.index(j as int))
                && spec_tm_at(
                    opts, ts, p, i1, (j + 1) as nat, jj, f1,
                ),
            TokenS::Alts(pats) => {
                // (?:kept_0|kept_1|...) zero-width only when every
                // branch was dropped; otherwise some kept branch k
                // matches p[j..mid) and the outer walk resumes at mid.
                // The (k, mid) pair is enumerated by a deterministic
                // branch-then-split tail scan (the exists-form resisted
                // the ground-evaluation lane -- the GL5 probe pinned the
                // positive-exists context-side instantiation failure --
                // so this arm is quantifier-free end to end).
                if pats.len() == 0 || !spec_pats_kept_scan(
                    opts, pats, pats.len() as nat, f1,
                )
                {
                    spec_tm_at(opts, ts, p, i1, j, jj, f1)
                } else {
                    spec_tm_alts_try(opts, ts, p, i, j, jj, pats, pats.len() as nat, f1)
                }
            },
        }
    }
}

/// The RecursivePrefix ".*/" arm: consume >= 1 chars, the last of them
/// a '/', then advance the token.
pub open spec fn spec_tm_recp_star(
    opts: GlobOptions,
    ts: Seq<TokenS>,
    p: Seq<char>,
    i: nat,
    j: nat,
    jj: nat,
    fuel: nat,
) -> bool
    decreases fuel
{
    if fuel == 0 || j as int >= jj as int {
        false
    } else if p.index(j as int) == '/' {
        // the `.*/` lane: the inner star (newline-permissive dot)
        // also eats '/', so this slash may close HERE or be eaten in
        // search of a later one (matchrec3/11/13/16 style
        // multi-component paths)
        spec_tm_at(opts, ts, p, (i + 1) as nat, (j + 1) as nat, jj, (fuel - 1) as nat)
            || spec_tm_recp_star(opts, ts, p, i, (j + 1) as nat, jj, (fuel - 1) as nat)
    } else {
        spec_tm_recp_star(opts, ts, p, i, (j + 1) as nat, jj, (fuel - 1) as nat)
    }
}

/// The "." star tail (RecS's `/.*` second lane, and the `**` special
/// case's `.*`): >= 0 any-chars, then the walk continues.
pub open spec fn spec_tm_dot_star(
    opts: GlobOptions,
    ts: Seq<TokenS>,
    p: Seq<char>,
    i: nat,
    j: nat,
    jj: nat,
    fuel: nat,
) -> bool
    decreases fuel
{
    if fuel == 0 {
        false
    } else {
        let j_i = j as int;
        let jj_i = jj as int;
        let f1 = (fuel - 1) as nat;
        let i1 = (i + 1) as nat;
        spec_tm_at(opts, ts, p, i1, j, jj, f1)
            || (j_i < jj_i && spec_tm_dot_star(opts, ts, p, i, (j + 1) as nat, jj, f1))
    }
}

/// The RecursiveZeroOrMore ".*/" tail: after the leading '/', some
/// >= 0 any-chars then a closing '/'.
pub open spec fn spec_tm_recz_tail(
    opts: GlobOptions,
    ts: Seq<TokenS>,
    p: Seq<char>,
    i: nat,
    j: nat,
    jj: nat,
    fuel: nat,
) -> bool
    decreases fuel
{
    if fuel == 0 {
        false
    } else {
        let j_i = j as int;
        let jj_i = jj as int;
        let f1 = (fuel - 1) as nat;
        let i1 = (i + 1) as nat;
        let j1 = (j + 1) as nat;
        if j_i >= jj_i {
            false
        } else if p.index(j as int) == '/' {
            // the `/.*/` closing slash: close here, or eat it and
            // search a later one (the inner chars include '/')
            spec_tm_at(opts, ts, p, i1, j1, jj, f1)
                || spec_tm_recz_tail(opts, ts, p, i, j1, jj, f1)
        } else {
            spec_tm_recz_tail(opts, ts, p, i, j1, jj, f1)
        }
    }
}

/// The `**`-alone special case: >= 0 any-chars reaching the path end.
pub open spec fn spec_tm_all_chars(p: Seq<char>, j: nat, fuel: nat) -> bool
    decreases fuel
{
    if j as int >= p.len() as int {
        true
    } else if fuel == 0 {
        false
    } else {
        spec_tm_all_chars(p, (j + 1) as nat, (fuel - 1) as nat)
    }
}

/// The Alternates branch scan: try each branch index top-down, every
/// step costs one fuel.
pub open spec fn spec_tm_alts_try(
    opts: GlobOptions,
    ts: Seq<TokenS>,
    p: Seq<char>,
    i: nat,
    j: nat,
    jj: nat,
    pats: Seq<Seq<TokenS>>,
    up_to: nat,
    fuel: nat,
) -> bool
    decreases fuel
{
    if fuel == 0 || up_to == 0 {
        false
    } else {
        spec_tm_mid_try(
            opts, ts, p, i, j, jj, pats, (up_to - 1) as nat, j, (fuel - 1) as nat,
        ) || spec_tm_alts_try(
            opts, ts, p, i, j, jj, pats, (up_to - 1) as nat, (fuel - 1) as nat,
        )
    }
}

/// The Alternates split-point scan for one branch k: every m in
/// [j, jj] is tried (kept(k) demanded at each; an unkept branch never
/// fires).
pub open spec fn spec_tm_mid_try(
    opts: GlobOptions,
    ts: Seq<TokenS>,
    p: Seq<char>,
    i: nat,
    j: nat,
    jj: nat,
    pats: Seq<Seq<TokenS>>,
    k: nat,
    m: nat,
    fuel: nat,
) -> bool
    decreases fuel
{
    if fuel == 0 {
        false
    } else {
        let m_i = m as int;
        let jj_i = jj as int;
        if m_i > jj_i {
            false
        } else {
            (spec_alts_branch_kept(
                opts, pats.index(k as int), (fuel - 1) as nat,
            ) && spec_tm_at(
                opts, pats.index(k as int), p, 0nat, j, m, (fuel - 1) as nat,
            ) && spec_tm_at(
                opts, ts, p, (i + 1) as nat, m, jj, (fuel - 1) as nat,
            )) || spec_tm_mid_try(
                opts, ts, p, i, j, jj, pats, k, (m + 1) as nat, (fuel - 1) as nat,
            )
        }
    }
}

// ---------------------------------------------------------------------------
// The Candidate char-twin faces (GL1's byte-domain pathutil projected
// one-to-one onto the char domain -- the valid-UTF-8 bridge of the D1
// charter; Candidate::from_cow lib.rs:642-648 is the constructor whose
// decision table these twins carry).
// ---------------------------------------------------------------------------

/// The last '/' in p[..up_to], if any (upwind budget = up_to).
pub open spec fn spec_last_slash_upto(p: Seq<char>, up_to: nat) -> Option<nat>
    decreases up_to
{
    if up_to == 0 {
        None
    } else if p.index((up_to - 1) as int) == '/' {
        // the current cell wins over the prefix: the scan returns the
        // LAST slash (rfind semantics, pathutil's rfind_byte)
        Some((up_to - 1) as nat)
    } else {
        spec_last_slash_upto(p, (up_to - 1) as nat)
    }
}

/// Origin Rust (pathutil.rs:8-28 -- doc carried verbatim):
///     /// The final component of the path, if it is a normal file.
///     ///
///     /// If the path terminates in `..`, or consists solely of a root of
///     /// prefix, file_name will return `None`.
///     pub(crate) fn file_name<'a>(path: &Cow<'a, [u8]>) -> Option<Cow<'a, [u8]>> {
///         if path.is_empty() { return None; }
///         let last_slash = path.rfind_byte(b'/').map(|i| i + 1).unwrap_or(0);
///         let got = ...&path[last_slash..];
///         if got == &b".."[..] { return None; }
///         Some(got)
///     }
/// (the GL1 byte face is already verified; this is its char twin, the
///  candidate-side carrier used by the strategic model.)
pub open spec fn spec_c_file_name(p: Seq<char>) -> Option<Seq<char>> {
    if p.len() == 0 {
        None
    } else {
        let cut = match spec_last_slash_upto(p, p.len() as nat) {
            Some(i) => (i + 1) as nat,
            None => 0nat,
        };
        let got = p.subrange(cut as int, p.len() as int);
        if got == seq!['.', '.'] {
            // the `..` rejection (pathutil.rs:18-20)
            None
        } else {
            Some(got)
        }
    }
}

/// from_cow's `file_name(&path).unwrap_or(Cow::Borrowed(B("")))` column
/// (lib.rs:643).
pub open spec fn spec_c_basename(p: Seq<char>) -> Seq<char> {
    match spec_c_file_name(p) {
        Some(b) => b,
        None => Seq::empty(),
    }
}

/// Origin Rust (pathutil.rs:30-52 -- the GM9 doc, carried verbatim):
///     /// Return a file extension given a path's file name.
///     ///
///     /// Note that this does NOT match the semantics of
///     /// std::path::Path::extension. Namely, the extension includes
///     /// the `.` and matching is otherwise more liberal. Specifically,
///     /// the extension is:
///     ///
///     /// * None, if the file name given is empty;
///     /// * None, if there is no embedded `.`;
///     /// * Otherwise, the portion of the file name starting with the
///     ///   final `.`.
///     ///
///     /// e.g., A file name of `.rs` has an extension `.rs`.
///     ///
///     /// N.B. This is done to make certain glob match optimizations
///     /// easier. Namely, a pattern like `*.rs` is obviously trying to
///     /// match files with a `rs` extension, but it also matches files
///     /// like `.rs`, which doesn't have an extension according to
///     /// std::path::Path::extension.
pub open spec fn spec_last_dot_upto(b: Seq<char>, up_to: nat) -> Option<nat>
    decreases up_to
{
    if up_to == 0 {
        None
    } else if b.index((up_to - 1) as int) == '.' {
        // current-cell priority: the LAST dot (file_name_ext's
        // rfind_byte)
        Some((up_to - 1) as nat)
    } else {
        spec_last_dot_upto(b, (up_to - 1) as nat)
    }
}

/// file_name_ext (pathutil.rs:39-52 body) over the char twin.
pub open spec fn spec_c_file_name_ext(b: Seq<char>) -> Option<Seq<char>> {
    if b.len() == 0 {
        None
    } else {
        match spec_last_dot_upto(b, b.len() as nat) {
            Some(i) => Some(b.subrange(i as int, b.len() as int)),
            None => None,
        }
    }
}

/// from_cow's `file_name_ext(&basename).unwrap_or(Cow::Borrowed(B("")))`
/// column (lib.rs:644).
pub open spec fn spec_c_ext(p: Seq<char>) -> Seq<char> {
    match spec_c_file_name_ext(spec_c_basename(p)) {
        Some(e) => e,
        None => Seq::empty(),
    }
}

/// Origin Rust (lib.rs:654-663 -- GM14's carrier, code comment and
/// inline note both verbatim; the analog `if self.basename.is_empty()
/// && self.path.ends_with(b"..")` is the raw path-ends_with, not a
/// basename property):
///     /// Returns the final component, including `..` for regex matching.
///     fn basename_for_regex(&self) -> &[u8] {
///         // Literal basename strategies skip `..`, but a regex can match it.
///         if self.basename.is_empty() && self.path.ends_with(b"..") {
///             b".."
///         } else {
///             &self.basename
///         }
///     }
pub open spec fn spec_c_base_for_regex(p: Seq<char>) -> Seq<char> {
    match spec_c_file_name(p) {
        None => {
            // basename empty AND the raw path ends with ".." -> the
            // regex arm reads the virtual basename ".."
            if p.len() >= 2 && p.subrange((p.len() - 2) as int, p.len() as int) == seq![
                '.',
                '.',
            ] {
                seq!['.', '.']
            } else {
                Seq::empty()
            }
        },
        Some(b) => b,
    }
}

/// Origin Rust (glob.rs:1086-1096, cfg(test) helpers, verbatim):
///     fn starts_with(needle: &[u8], haystack: &[u8]) -> bool {
///         needle.len() <= haystack.len() && needle == &haystack[..needle.len()]
///     }
///     fn ends_with(needle: &[u8], haystack: &[u8]) -> bool {
///         if needle.len() > haystack.len() { return false; }
///         needle == &haystack[haystack.len() - needle.len()..]
///     }
/// (char twins; the byte original and the char twin agree on the
///  valid-UTF-8 face -- UTF-8 is prefix- and suffix-stable.)
pub open spec fn spec_c_starts_with(pre: Seq<char>, p: Seq<char>) -> bool {
    pre.len() <= p.len() && p.subrange(0, pre.len() as int) == pre
}

pub open spec fn spec_c_ends_with(suf: Seq<char>, p: Seq<char>) -> bool {
    suf.len() <= p.len() && p.subrange((p.len() - suf.len()) as int, p.len() as int) == suf
}

// ---------------------------------------------------------------------------
// The GlobStrategic is_match_candidate twin: glob.rs:172-205, arm
// order and every conjunct verbatim (quoted in the notes' per-arm
// Origin table). The regex-consuming arms (RequiredExtension's
// self.re.is_match, BasenameRegex's self.re.is_match over
// basename_for_regex, and the Regex fallback) read the token-model
// matcher instead of the byte regex -- that substitution is precisely
// the weld; GM10's emission-faithfulness half plus the P6 boundary
// (the regex-engine equivalence itself stays oracle-assertion domain)
// carry the value lock.
// ---------------------------------------------------------------------------

pub open spec fn spec_strat_check(
    opts: GlobOptions,
    strat: MatchStrategyS,
    ts: Seq<TokenS>,
    p: Seq<char>,
    fuel: nat,
) -> bool {
    match strat {
        MatchStrategyS::Literal(lit) => p == lit,
        MatchStrategyS::BasenameLiteral(lit) => spec_c_basename(p) == lit,
        MatchStrategyS::Extension(e) => spec_c_ext(p) == e,
        MatchStrategyS::Prefix(pre) => spec_c_starts_with(pre, p),
        MatchStrategyS::Suffix { suffix, component } => {
            // glob.rs:194-198:
            //   if component && byte_path == &suffix.as_bytes()[1..] {
            //       return true;
            //   }
            //   ends_with(suffix.as_bytes(), byte_path)
            if component && p == suffix.subrange(1, suffix.len() as int) {
                true
            } else {
                spec_c_ends_with(suffix, p)
            }
        },
        MatchStrategyS::RequiredExtension(e) => {
            // glob.rs:199-202:
            //   let ext = ext.as_bytes();
            //   &*candidate.ext == ext && self.re.is_match(byte_path)
            spec_c_ext(p) == e && spec_tokens_match(opts, ts, p, fuel)
        },
        MatchStrategyS::BasenameRegex(_) => {
            // glob.rs:203-204:
            //   self.re.is_match(candidate.basename_for_regex())
            // where self.re was compiled from the basename token slice
            match spec_basename_tokens(opts, ts) {
                Some(slice) => spec_tokens_match(opts, slice, spec_c_base_for_regex(p), fuel),
                None => false,
            }
        },
        MatchStrategyS::Regex => spec_tokens_match(opts, ts, p, fuel),
    }
}

} // verus!

/// Single-file driver anchor (consumers reference this file via #[path]).
fn main() {}
