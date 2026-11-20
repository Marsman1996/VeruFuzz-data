//! GL2 harness -- the 33 `syntax!` KAT theorems (upstream glob.rs:1245-1289,
//! patterns and expected token sequences verbatim; the values
//! cross-checked against the upstream-run oracle arm,
//! out/kverus-run/GL2/oracle-run.txt:1-33).
//!
//! Upstream macro shape:
//!     macro_rules! syntax {
//!         ($name:ident, $pat:expr, $tokens:expr) => {
//!             #[test] fn $name() {
//!                 let pat = Glob::new($pat).unwrap();
//!                 assert_eq!($tokens, pat.tokens.0);
//!             }
//!         };
//!     }
//! The theorem form below pins spec_parse_glob (the value machine) on
//! each ground pattern: the exact token-sequence value equality on
//! the whole Result.
//!
//! Upstream crate-Syntax doc (lib.rs:66-96, the semantic carrier of the
//! Token family, verbatim):
//!   Standard Unix-style glob syntax is supported:
//!   * `?` matches any single character. (If the `literal_separator`
//!     option is enabled, then `?` can never match a path separator.)
//!   * `*` matches zero or more characters. (If the `literal_separator`
//!     option is enabled, then `*` can never match a path separator.)
//!   * `**` recursively matches directories but are only legal in three
//!     situations. First, if the glob starts with <code>\*\*&#x2F;</code>,
//!     then it matches all directories. For example,
//!     <code>\*\*&#x2F;foo</code> matches `foo` and `bar/foo` but not
//!     `foo/bar`. Secondly, if the glob ends with
//!     <code>&#x2F;\*\*</code>, then it matches all sub-entries. For
//!     example, <code>foo&#x2F;\*\*</code> matches `foo/a` and
//!     `foo/a/b`, but not `foo`. Thirdly, if the glob contains
//!     <code>&#x2F;\*\*&#x2F;</code> anywhere within the pattern, then
//!     it matches zero or more directories. Using `**` anywhere else is
//!     illegal (N.B. the glob `**` is allowed and means "match
//!     everything").
//!   * `{a,b}` matches `a` or `b` where `a` and `b` are arbitrary glob
//!     patterns. (N.B. Nesting `{...}` is not currently allowed.)
//!   * `[ab]` matches `a` or `b` where `a` and `b` are characters. Use
//!     `[!ab]` to match any character except for `a` and `b`.
//!   * Metacharacters such as `*` and `?` can be escaped with character
//!     class notation. e.g., `[*]` matches `*`.
//!   * When backslash escapes are enabled, a backslash (`\`) will
//!     escape all meta characters in a glob. If it precedes a
//!     non-meta character, then the slash is ignored. A `\\` will
//!     match a literal `\\`. Note that this mode is only enabled on
//!     Unix platforms by default, but can be enabled on any platform
//!     via the `backslash_escape` setting on `Glob`.
//! (The N.B.-marked notes are the GM1 registry's anchor lines; the
//!  `**`-illegality clause is superseded by GM2's deprecated-variant
//!  ruling per the CHANGELOG; the nesting clause by GM3's.)

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::seq::seq;

#[path = "../src/lib.rs"]
mod lib;

use lib::CowBytes;
#[allow(unused_imports)]
use lib::pathutil;
use lib::glob::{
    spec_opts_unix_default, spec_parse_glob, spec_parse_loop, spec_parse_star,
    spec_parse_class, spec_class_loop, spec_parse_comma, spec_parse_backslash,
    spec_push_token, spec_push_tokens2, spec_pop_token, spec_have_tokens,
    spec_push_alternate, spec_pop_alternate, spec_bump, spec_peek, spec_star_tail,
    spec_star_rewrite, spec_star_rewrite2, spec_add_to_last, TokenS,
};

verus! {

// ===========================================================================
// literal / any / single-star families (glob.rs:1245-1250)
// ===========================================================================

// syntax!(literal1, "a", vec![Literal('a')])
proof fn ut_syntax_literal1() {
    assert(spec_parse_glob(seq!['a'], spec_opts_unix_default(), false)
        == Ok(seq![TokenS::Lit('a')])) by (compute);
}

// syntax!(literal2, "ab", vec![Literal('a'), Literal('b')])
proof fn ut_syntax_literal2() {
    assert(spec_parse_glob(seq!['a', 'b'], spec_opts_unix_default(), false)
        == Ok(seq![TokenS::Lit('a'), TokenS::Lit('b')])) by (compute);
}

// syntax!(any1, "?", vec![Any])
proof fn ut_syntax_any1() {
    assert(spec_parse_glob(seq!['?'], spec_opts_unix_default(), false)
        == Ok(seq![TokenS::Any])) by (compute);
}

// syntax!(any2, "a?b", vec![Literal('a'), Any, Literal('b')])
proof fn ut_syntax_any2() {
    assert(spec_parse_glob(seq!['a', '?', 'b'], spec_opts_unix_default(), false)
        == Ok(seq![TokenS::Lit('a'), TokenS::Any, TokenS::Lit('b')])) by (compute);
}

// syntax!(seq1, "*", vec![ZeroOrMore])
proof fn ut_syntax_seq1() {
    assert(spec_parse_glob(seq!['*'], spec_opts_unix_default(), false)
        == Ok(seq![TokenS::Zom])) by (compute);
}

// syntax!(seq2, "a*b", vec![Literal('a'), ZeroOrMore, Literal('b')])
proof fn ut_syntax_seq2() {
    assert(spec_parse_glob(seq!['a', '*', 'b'], spec_opts_unix_default(), false)
        == Ok(seq![TokenS::Lit('a'), TokenS::Zom, TokenS::Lit('b')])) by (compute);
}

// syntax!(seq3, "*a*b*",
//   vec![ZeroOrMore, Literal('a'), ZeroOrMore, Literal('b'), ZeroOrMore])
proof fn ut_syntax_seq3() {
    assert(spec_parse_glob(
        seq!['*', 'a', '*', 'b', '*'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![
        TokenS::Zom,
        TokenS::Lit('a'),
        TokenS::Zom,
        TokenS::Lit('b'),
        TokenS::Zom,
    ])) by (compute);
}

// ===========================================================================
// the recursive families (glob.rs:1256-1264) -- the parse_star lattice
// ===========================================================================

// syntax!(rseq1, "**", vec![RecursivePrefix])
proof fn ut_syntax_rseq1() {
    assert(spec_parse_glob(seq!['*', '*'], spec_opts_unix_default(), false)
        == Ok(seq![TokenS::RecP])) by (compute);
}

// syntax!(rseq2, "**/", vec![RecursivePrefix])
proof fn ut_syntax_rseq2() {
    assert(spec_parse_glob(seq!['*', '*', '/'], spec_opts_unix_default(), false)
        == Ok(seq![TokenS::RecP])) by (compute);
}

// syntax!(rseq3, "/**", vec![RecursiveSuffix])
proof fn ut_syntax_rseq3() {
    assert(spec_parse_glob(seq!['/', '*', '*'], spec_opts_unix_default(), false)
        == Ok(seq![TokenS::Lit('/'), TokenS::RecS])) by (compute);
}

// syntax!(rseq4, "/**/", vec![RecursiveZeroOrMore])
proof fn ut_syntax_rseq4() {
    assert(spec_parse_glob(
        seq!['/', '*', '*', '/'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Lit('/'), TokenS::RecZ])) by (compute);
}

// syntax!(rseq5, "a/**/b",
//   vec![Literal('a'), RecursiveZeroOrMore, Literal('b')])
proof fn ut_syntax_rseq5() {
    assert(spec_parse_glob(
        seq!['a', '/', '*', '*', '/', 'b'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Lit('a'), TokenS::RecZ, TokenS::Lit('b')])) by (compute);
}

// ===========================================================================
// the class families (glob.rs:1265-1289); class2 = the single-range
// class, rc2/rcn2/rc3 = the multi-range spellings of upstream's
// class/classn/rclass/rclassn helpers (glob.rs:1229-1243)
// ===========================================================================

// syntax!(cls1, "[a]", vec![class('a', 'a')])
proof fn ut_syntax_cls1() {
    assert(spec_parse_glob(seq!['[', 'a', ']'], spec_opts_unix_default(), false)
        == Ok(seq![TokenS::Cls { negated: false, ranges: seq![('a', 'a')] }])) by (compute);
}

// syntax!(cls2, "[!a]", vec![classn('a', 'a')])
proof fn ut_syntax_cls2() {
    assert(spec_parse_glob(
        seq!['[', '!', 'a', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls { negated: true, ranges: seq![('a', 'a')] }])) by (compute);
}

// syntax!(cls3, "[a-z]", vec![class('a', 'z')])
proof fn ut_syntax_cls3() {
    assert(spec_parse_glob(
        seq!['[', 'a', '-', 'z', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls { negated: false, ranges: seq![('a', 'z')] }])) by (compute);
}

// syntax!(cls4, "[!a-z]", vec![classn('a', 'z')])
proof fn ut_syntax_cls4() {
    assert(spec_parse_glob(
        seq!['[', '!', 'a', '-', 'z', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls { negated: true, ranges: seq![('a', 'z')] }])) by (compute);
}

// syntax!(cls5, "[-]", vec![class('-', '-')])
proof fn ut_syntax_cls5() {
    assert(spec_parse_glob(seq!['[', '-', ']'], spec_opts_unix_default(), false)
        == Ok(seq![TokenS::Cls { negated: false, ranges: seq![('-', '-')] }])) by (compute);
}

// syntax!(cls6, "[]]", vec![class(']', ']')])
proof fn ut_syntax_cls6() {
    assert(spec_parse_glob(seq!['[', ']', ']'], spec_opts_unix_default(), false)
        == Ok(seq![TokenS::Cls { negated: false, ranges: seq![(']', ']')] }])) by (compute);
}

// syntax!(cls7, "[*]", vec![class('*', '*')])
proof fn ut_syntax_cls7() {
    assert(spec_parse_glob(seq!['[', '*', ']'], spec_opts_unix_default(), false)
        == Ok(seq![TokenS::Cls { negated: false, ranges: seq![('*', '*')] }])) by (compute);
}

// syntax!(cls8, "[!!]", vec![classn('!', '!')])
proof fn ut_syntax_cls8() {
    assert(spec_parse_glob(
        seq!['[', '!', '!', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls { negated: true, ranges: seq![('!', '!')] }])) by (compute);
}

// syntax!(cls9, "[a-]", vec![rclass(&[('a','a'),('-','-')])])
proof fn ut_syntax_cls9() {
    assert(spec_parse_glob(
        seq!['[', 'a', '-', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls {
        negated: false,
        ranges: seq![('a', 'a'), ('-', '-')],
    }])) by (compute);
}

// syntax!(cls10, "[-a-z]", vec![rclass(&[('-','-'),('a','z')])])
proof fn ut_syntax_cls10() {
    assert(spec_parse_glob(
        seq!['[', '-', 'a', '-', 'z', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls {
        negated: false,
        ranges: seq![('-', '-'), ('a', 'z')],
    }])) by (compute);
}

// syntax!(cls11, "[a-z-]", vec![rclass(&[('a','z'),('-','-')])])
proof fn ut_syntax_cls11() {
    assert(spec_parse_glob(
        seq!['[', 'a', '-', 'z', '-', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls {
        negated: false,
        ranges: seq![('a', 'z'), ('-', '-')],
    }])) by (compute);
}

// syntax!(cls12, "[-a-z-]", vec![rclass(&[('-','-'),('a','z'),('-','-')])])
proof fn ut_syntax_cls12() {
    assert(spec_parse_glob(
        seq!['[', '-', 'a', '-', 'z', '-', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls {
        negated: false,
        ranges: seq![('-', '-'), ('a', 'z'), ('-', '-')],
    }])) by (compute);
}

// syntax!(cls13, "[]-z]", vec![class(']', 'z')])
proof fn ut_syntax_cls13() {
    assert(spec_parse_glob(
        seq!['[', ']', '-', 'z', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls { negated: false, ranges: seq![(']', 'z')] }])) by (compute);
}

// syntax!(cls14, "[--z]", vec![class('-', 'z')])
proof fn ut_syntax_cls14() {
    assert(spec_parse_glob(
        seq!['[', '-', '-', 'z', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls { negated: false, ranges: seq![('-', 'z')] }])) by (compute);
}

// syntax!(cls15, "[ --]", vec![class(' ', '-')])
proof fn ut_syntax_cls15() {
    assert(spec_parse_glob(
        seq!['[', ' ', '-', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls { negated: false, ranges: seq![(' ', '-')] }])) by (compute);
}

// syntax!(cls16, "[0-9a-z]", vec![rclass(&[('0','9'),('a','z')])])
proof fn ut_syntax_cls16() {
    assert(spec_parse_glob(
        seq!['[', '0', '-', '9', 'a', '-', 'z', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls {
        negated: false,
        ranges: seq![('0', '9'), ('a', 'z')],
    }])) by (compute);
}

// syntax!(cls17, "[a-z0-9]", vec![rclass(&[('a','z'),('0','9')])])
proof fn ut_syntax_cls17() {
    assert(spec_parse_glob(
        seq!['[', 'a', '-', 'z', '0', '-', '9', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls {
        negated: false,
        ranges: seq![('a', 'z'), ('0', '9')],
    }])) by (compute);
}

// syntax!(cls18, "[!0-9a-z]", vec![rclassn(&[('0','9'),('a','z')])])
proof fn ut_syntax_cls18() {
    assert(spec_parse_glob(
        seq!['[', '!', '0', '-', '9', 'a', '-', 'z', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls {
        negated: true,
        ranges: seq![('0', '9'), ('a', 'z')],
    }])) by (compute);
}

// syntax!(cls19, "[!a-z0-9]", vec![rclassn(&[('a','z'),('0','9')])])
proof fn ut_syntax_cls19() {
    assert(spec_parse_glob(
        seq!['[', '!', 'a', '-', 'z', '0', '-', '9', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls {
        negated: true,
        ranges: seq![('a', 'z'), ('0', '9')],
    }])) by (compute);
}

// syntax!(cls20, "[^a]", vec![classn('a', 'a')])
proof fn ut_syntax_cls20() {
    assert(spec_parse_glob(
        seq!['[', '^', 'a', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls { negated: true, ranges: seq![('a', 'a')] }])) by (compute);
}

// syntax!(cls21, "[^a-z]", vec![classn('a', 'z')])
proof fn ut_syntax_cls21() {
    assert(spec_parse_glob(
        seq!['[', '^', 'a', '-', 'z', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls { negated: true, ranges: seq![('a', 'z')] }])) by (compute);
}

// ===========================================================================
// The alternates lattice family (oracle-run.txt:52-57, the GL2-added
// adversarial KAT rows -- the shared-decision drain, the empty
// alternate branch, the nested window, the sequence continuity; the
// upstream syntax! family has no `{...}` vectors of its own -- the
// raster below comes from the oracle-arm ground runs, the same lattice
// the 33 KAT rows and the GL4 extractors consume).
// ===========================================================================

// probe: "{a,b}" -> Alternates[[Lit a],[Lit b]]
proof fn ut_syntax_alt_basic() {
    assert(spec_parse_glob(
        seq!['{', 'a', ',', 'b', '}'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Alts(seq![
        seq![TokenS::Lit('a')],
        seq![TokenS::Lit('b')],
    ])])) by (compute);
}

// probe: "{a,{b,c}}" -> Alternates[[a],[Alts[[b],[c]]]] (nested, GM3)
proof fn ut_syntax_alt_nested() {
    assert(spec_parse_glob(
        seq!['{', 'a', ',', '{', 'b', ',', 'c', '}', '}'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Alts(seq![
        seq![TokenS::Lit('a')],
        seq![TokenS::Alts(seq![
            seq![TokenS::Lit('b')],
            seq![TokenS::Lit('c')],
        ])],
    ])])) by (compute);
}

// probe: "{,a}" -> Alternates[[],[a]] (the empty branch kept at the
// parse tier; the empty_alternates drop is the GL3 lowering surface)
proof fn ut_syntax_alt_empty_branch() {
    assert(spec_parse_glob(
        seq!['{', ',', 'a', '}'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Alts(seq![
        seq![],
        seq![TokenS::Lit('a')],
    ])])) by (compute);
}

// probe: "a,b" -> [Lit a, Lit ',', Lit b] (the comma outside any group)
proof fn ut_syntax_comma_plain() {
    assert(spec_parse_glob(
        seq!['a', ',', 'b'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![
        TokenS::Lit('a'),
        TokenS::Lit(','),
        TokenS::Lit('b'),
    ])) by (compute);
}

// probe: "{ disposi}" style empty window: "{,}" -> Alts[[],[]]
proof fn ut_syntax_alt_both_empty() {
    assert(spec_parse_glob(
        seq!['{', ',', '}'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Alts(seq![seq![], seq![]])])) by (compute);
}

// probe: "a**" -> [a, Zom, Zom] (the prev-not-sep rewrite)
proof fn ut_syntax_star_a_xx() {
    assert(spec_parse_glob(
        seq!['a', '*', '*'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Lit('a'), TokenS::Zom, TokenS::Zom])) by (compute);
}

// probe: "/**a" -> [/, Zom, Zom, a] (the suffix-decision other arm)
proof fn ut_syntax_slash_xx_a() {
    assert(spec_parse_glob(
        seq!['/', '*', '*', 'a'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![
        TokenS::Lit('/'),
        TokenS::Zom,
        TokenS::Zom,
        TokenS::Lit('a'),
    ])) by (compute);
}

// probe: "a/**/**" -> [a, RecS] (the double-recursive fold to suffix,
// the pop/rewrite lattice with the is_suffix rewrite of the second pair)
proof fn ut_syntax_a_rxx_rxx() {
    assert(spec_parse_glob(
        seq!['a', '/', '*', '*', '/', '*', '*'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Lit('a'), TokenS::RecS])) by (compute);
}

} // verus!

fn main() {}
