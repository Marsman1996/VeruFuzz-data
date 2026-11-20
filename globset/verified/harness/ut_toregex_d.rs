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
// toregex!(re9, "[+]", ^[\+]$, DEF)
proof fn ut_toregex_re9() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['[', '+', ']'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '[', '\\', '+', ']', '$']) by (compute);
}

// toregex!(re10, "+", ^\+$, DEF)
proof fn ut_toregex_re10() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['+'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '\\', '+', '$']) by (compute);
}

// toregex!(re11, "☃", ^\xe2\x98\x83$, DEF)
proof fn ut_toregex_re11() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['☃'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '\\', 'x', 'e', '2', '\\', 'x', '9', '8', '\\', 'x', '8', '3', '$']) by (compute);
}

// toregex!(re12, "**", ^.*$, DEF)
proof fn ut_toregex_re12() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['*', '*'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '.', '*', '$']) by (compute);
}

// toregex!(re13, "**/", ^.*$, DEF)
proof fn ut_toregex_re13() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['*', '*', '/'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '.', '*', '$']) by (compute);
}

// toregex!(re14, "**/*", ^(?:/?|.*/).*$, DEF)
proof fn ut_toregex_re14() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['*', '*', '/', '*'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '(', '?', ':', '/', '?', '|', '.', '*', '/', ')', '.', '*', '$']) by (compute);
}

// toregex!(re15, "**/**", ^.*$, DEF)
proof fn ut_toregex_re15() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['*', '*', '/', '*', '*'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '.', '*', '$']) by (compute);
}

// toregex!(re16, "**/**/*", ^(?:/?|.*/).*$, DEF)
proof fn ut_toregex_re16() {
    let opts = spec_opts_unix_default();
    let parsed = spec_parse_glob(seq!['*', '*', '/', '*', '*', '/', '*'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '(', '?', ':', '/', '?', '|', '.', '*', '/', ')', '.', '*', '$']) by (compute);
}


} // verus!

fn main() {}
