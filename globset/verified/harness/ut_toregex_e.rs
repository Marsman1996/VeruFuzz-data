//! GL3 harness -- the 8 `toregex!` KAT theorems (upstream
//! glob.rs:1345-1413 fixtures verbatim; expected strings are the
//! upstream test file's OWN $re literals, the prologue prepended per
//! the macro's format!("(?-u){}", $re) column). The theorem pins
//! the composition spec_parse_glob (the GL2 machine, the fixture's
//! options) with .. spec_to_regex_with (the GL3 emission family) on
//! each ground pattern, fuel = 64 (above any vector's depth; the
//! full-string equality certifies the fuel never truncated a run).
//! Fixture-count note: the upstream test block has exactly 50
//! toregex call sites -- harness-inventory.md's "51 vectors" also
//! counts the macro's internal recursive arm (glob.rs:1135).
//! Options columns: default Options (no setters).

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::seq::seq;

#[path = "../src/lib.rs"]
mod lib;

#[allow(unused_imports)]
use lib::CowBytes;
#[allow(unused_imports)]
use lib::pathutil;
use lib::glob::{
    spec_opts_unix_default, spec_parse_glob, spec_to_regex_with, GlobOptions, TokenS,
};

verus!
{
// toregex!(re17, "**/**/**", ^.*$, DEF)
proof fn ut_toregex_re17() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['*', '*', '/', '*', '*', '/', '*', '*'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '.', '*', '$']) by (compute);
}

// toregex!(re18, "**/**/**/*", ^(?:/?|.*/).*$, DEF)
proof fn ut_toregex_re18() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['*', '*', '/', '*', '*', '/', '*', '*', '/', '*'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '(', '?', ':', '/', '?', '|', '.', '*', '/', ')', '.', '*', '$']) by (compute);
}

// toregex!(re19, "a/**", ^a/.*$, DEF)
proof fn ut_toregex_re19() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['a', '/', '*', '*'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', 'a', '/', '.', '*', '$']) by (compute);
}

// toregex!(re20, "a/**/**", ^a/.*$, DEF)
proof fn ut_toregex_re20() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['a', '/', '*', '*', '/', '*', '*'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', 'a', '/', '.', '*', '$']) by (compute);
}

// toregex!(re21, "a/**/**/**", ^a/.*$, DEF)
proof fn ut_toregex_re21() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['a', '/', '*', '*', '/', '*', '*', '/', '*', '*'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', 'a', '/', '.', '*', '$']) by (compute);
}

// toregex!(re22, "a/**/b", ^a(?:/|/.*/)b$, DEF)
proof fn ut_toregex_re22() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['a', '/', '*', '*', '/', 'b'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', 'a', '(', '?', ':', '/', '|', '/', '.', '*', '/', ')', 'b', '$']) by (compute);
}

// toregex!(re23, "a/**/**/b", ^a(?:/|/.*/)b$, DEF)
proof fn ut_toregex_re23() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['a', '/', '*', '*', '/', '*', '*', '/', 'b'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', 'a', '(', '?', ':', '/', '|', '/', '.', '*', '/', ')', 'b', '$']) by (compute);
}

// toregex!(re24, "a/**/**/**/b", ^a(?:/|/.*/)b$, DEF)
proof fn ut_toregex_re24() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['a', '/', '*', '*', '/', '*', '*', '/', '*', '*', '/', 'b'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', 'a', '(', '?', ':', '/', '|', '/', '.', '*', '/', ')', 'b', '$']) by (compute);
}


} // verus!

fn main() {}
