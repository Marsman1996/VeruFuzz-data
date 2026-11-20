//! GL2 harness -- the 10 `syntaxerr!` KAT theorems (upstream
//! glob.rs:1291-1300, patterns and expected kinds verbatim; the kinds
//! cross-checked against the upstream-run oracle arm,
//! out/kverus-run/GL2/oracle-run.txt:34-43).
//!
//! Upstream macro shape:
//!     macro_rules! syntaxerr {
//!         ($name:ident, $pat:expr, $err:expr) => {
//!             #[test] fn $name() {
//!                 let err = Glob::new($pat).unwrap_err();
//!                 assert_eq!(&$err, err.kind());
//!             }
//!         };
//!     }
//! The theorem form below pins spec_parse_glob's Err arm: the exact
//! ErrorKind value (upstream asserts kind equality; the glob-pattern
//! reference column of the twin rides the caller-visible pattern,
//! see the GL8 deferred ledger).

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
    spec_star_rewrite, spec_star_rewrite2, spec_add_to_last, is_parse_error,
    ErrorKind, TokenS,
};

verus! {

// syntaxerr!(err_unclosed1, "[", ErrorKind::UnclosedClass)
proof fn ut_syntaxerr_unclosed1() {
    assert(spec_parse_glob(seq!['['], spec_opts_unix_default(), false)
        == Err(ErrorKind::UnclosedClass)) by (compute);
}

// syntaxerr!(err_unclosed2, "[]", ErrorKind::UnclosedClass)
proof fn ut_syntaxerr_unclosed2() {
    assert(spec_parse_glob(seq!['[', ']'], spec_opts_unix_default(), false)
        == Err(ErrorKind::UnclosedClass)) by (compute);
}

// syntaxerr!(err_unclosed3, "[!", ErrorKind::UnclosedClass)
proof fn ut_syntaxerr_unclosed3() {
    assert(spec_parse_glob(seq!['[', '!'], spec_opts_unix_default(), false)
        == Err(ErrorKind::UnclosedClass)) by (compute);
}

// syntaxerr!(err_unclosed4, "[!]", ErrorKind::UnclosedClass)
proof fn ut_syntaxerr_unclosed4() {
    assert(spec_parse_glob(seq!['[', '!', ']'], spec_opts_unix_default(), false)
        == Err(ErrorKind::UnclosedClass)) by (compute);
}

// syntaxerr!(err_range1, "[z-a]", ErrorKind::InvalidRange('z', 'a'))
proof fn ut_syntaxerr_range1() {
    assert(spec_parse_glob(
        seq!['[', 'z', '-', 'a', ']'],
        spec_opts_unix_default(),
        false,
    ) == Err(ErrorKind::InvalidRange('z', 'a'))) by (compute);
}

// syntaxerr!(err_range2, "[z--]", ErrorKind::InvalidRange('z', '-'))
proof fn ut_syntaxerr_range2() {
    assert(spec_parse_glob(
        seq!['[', 'z', '-', '-', ']'],
        spec_opts_unix_default(),
        false,
    ) == Err(ErrorKind::InvalidRange('z', '-'))) by (compute);
}

// syntaxerr!(err_alt1, "{a,b", ErrorKind::UnclosedAlternates)
proof fn ut_syntaxerr_alt1() {
    assert(spec_parse_glob(
        seq!['{', 'a', ',', 'b'],
        spec_opts_unix_default(),
        false,
    ) == Err(ErrorKind::UnclosedAlternates)) by (compute);
}

// syntaxerr!(err_alt2, "{a,{b,c}", ErrorKind::UnclosedAlternates)
proof fn ut_syntaxerr_alt2() {
    assert(spec_parse_glob(
        seq!['{', 'a', ',', '{', 'b', ',', 'c', '}'],
        spec_opts_unix_default(),
        false,
    ) == Err(ErrorKind::UnclosedAlternates)) by (compute);
}

// syntaxerr!(err_alt3, "a,b}", ErrorKind::UnopenedAlternates)
proof fn ut_syntaxerr_alt3() {
    assert(spec_parse_glob(
        seq!['a', ',', 'b', '}'],
        spec_opts_unix_default(),
        false,
    ) == Err(ErrorKind::UnopenedAlternates)) by (compute);
}

// syntaxerr!(err_alt4, "{a,b}}", ErrorKind::UnopenedAlternates)
proof fn ut_syntaxerr_alt4() {
    assert(spec_parse_glob(
        seq!['{', 'a', ',', 'b', '}', '}'],
        spec_opts_unix_default(),
        false,
    ) == Err(ErrorKind::UnopenedAlternates)) by (compute);
}

// ===========================================================================
// GL2-added adversarial error rows (oracle-run.txt:60-62,65 -- the
// backslash-exhaustion column and the negated-empty class corner)
// ===========================================================================

// probe: "\" (single backslash) -> DanglingEscape (the bump at the
// end returns None under the escape option)
proof fn ut_syntaxerr_dangling_bs() {
    assert(spec_parse_glob(seq!['\\'], spec_opts_unix_default(), false)
        == Err(ErrorKind::DanglingEscape)) by (compute);
}

// probe: "a\" -> DanglingEscape
proof fn ut_syntaxerr_dangling_bs2() {
    assert(spec_parse_glob(seq!['a', '\\'], spec_opts_unix_default(), false)
        == Err(ErrorKind::DanglingEscape)) by (compute);
}

// probe: "[a-\\]" -> InvalidRange('a', '\\') (the range-extension
// order check across the escaped literal)
proof fn ut_syntaxerr_range_bs() {
    assert(spec_parse_glob(
        seq!['[', 'a', '-', '\\', ']'],
        spec_opts_unix_default(),
        false,
    ) == Err(ErrorKind::InvalidRange('a', '\\'))) by (compute);
}

// probe: "[^]" -> UnclosedClass (the '^' negation consumes; the ']'
// closes? No: after '^', ']' is the FIRST class char -> literal ']' ->
// exhaustion)
proof fn ut_syntaxerr_negated_empty() {
    assert(spec_parse_glob(
        seq!['[', '^', ']'],
        spec_opts_unix_default(),
        false,
    ) == Err(ErrorKind::UnclosedClass)) by (compute);
}

// probe: "abc,d}" -> UnopenedAlternates (the comma outside a group
// stays a literal; the stray '}' pops the empty stack)
proof fn ut_syntaxerr_alt5() {
    assert(spec_parse_glob(
        seq!['a', 'b', 'c', ',', 'd', '}'],
        spec_opts_unix_default(),
        false,
    ) == Err(ErrorKind::UnopenedAlternates)) by (compute);
}

} // verus!

fn main() {}
