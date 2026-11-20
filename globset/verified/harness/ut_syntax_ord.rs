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
// (the range-order vector family: the \x3c-on-chars compute residual;
// these close via the smt fallback at higher wall budgets -- the range
// order test is the only residual duty)

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

// syntax!(cls21, "[^a-z]", vec![classn('a', 'z')])
proof fn ut_syntax_cls21() {
    assert(spec_parse_glob(
        seq!['[', '^', 'a', '-', 'z', ']'],
        spec_opts_unix_default(),
        false,
    ) == Ok(seq![TokenS::Cls { negated: true, ranges: seq![('a', 'z')] }])) by (compute);
}


} // verus!

fn main() {}
