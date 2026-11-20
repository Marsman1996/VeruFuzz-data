//! GL3 harness -- the 9 `toregex!` KAT theorems (upstream
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
//! Options columns: UNCCLS = allow_unclosed_class applied.

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
// toregex!(allow_unclosed_class_single, "[", ^\[$, UNCCLS)
proof fn ut_toregex_allow_unclosed_class_single() {
    let opts = GlobOptions { allow_unclosed_class: true, ..spec_opts_unix_default() };
    let parsed = spec_parse_glob(seq!['['], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '\\', '[', '$']) by (compute);
}

// toregex!(allow_unclosed_class_many, "[abc", ^\[abc$, UNCCLS)
proof fn ut_toregex_allow_unclosed_class_many() {
    let opts = GlobOptions { allow_unclosed_class: true, ..spec_opts_unix_default() };
    let parsed = spec_parse_glob(seq!['[', 'a', 'b', 'c'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '\\', '[', 'a', 'b', 'c', '$']) by (compute);
}

// toregex!(allow_unclosed_class_empty1, "[]", ^\[\]$, UNCCLS)
proof fn ut_toregex_allow_unclosed_class_empty1() {
    let opts = GlobOptions { allow_unclosed_class: true, ..spec_opts_unix_default() };
    let parsed = spec_parse_glob(seq!['[', ']'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '\\', '[', '\\', ']', '$']) by (compute);
}

// toregex!(allow_unclosed_class_empty2, "[][", ^\[\]\[$, UNCCLS)
proof fn ut_toregex_allow_unclosed_class_empty2() {
    let opts = GlobOptions { allow_unclosed_class: true, ..spec_opts_unix_default() };
    let parsed = spec_parse_glob(seq!['[', ']', '['], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '\\', '[', '\\', ']', '\\', '[', '$']) by (compute);
}

// toregex!(allow_unclosed_class_negated_unclosed, "[!", ^\[!$, UNCCLS)
proof fn ut_toregex_allow_unclosed_class_negated_unclosed() {
    let opts = GlobOptions { allow_unclosed_class: true, ..spec_opts_unix_default() };
    let parsed = spec_parse_glob(seq!['[', '!'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '\\', '[', '!', '$']) by (compute);
}

// toregex!(allow_unclosed_class_negated_empty, "[!]", ^\[!\]$, UNCCLS)
proof fn ut_toregex_allow_unclosed_class_negated_empty() {
    let opts = GlobOptions { allow_unclosed_class: true, ..spec_opts_unix_default() };
    let parsed = spec_parse_glob(seq!['[', '!', ']'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '\\', '[', '!', '\\', ']', '$']) by (compute);
}

// toregex!(allow_unclosed_class_brace1, "{[abc,xyz}", ^(?:\[abc|xyz)$, UNCCLS)
proof fn ut_toregex_allow_unclosed_class_brace1() {
    let opts = GlobOptions { allow_unclosed_class: true, ..spec_opts_unix_default() };
    let parsed = spec_parse_glob(seq!['{', '[', 'a', 'b', 'c', ',', 'x', 'y', 'z', '}'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '(', '?', ':', '\\', '[', 'a', 'b', 'c', '|', 'x', 'y', 'z', ')', '$']) by (compute);
}

// toregex!(allow_unclosed_class_brace2, "{[abc,[xyz}", ^(?:\[abc|\[xyz)$, UNCCLS)
proof fn ut_toregex_allow_unclosed_class_brace2() {
    let opts = GlobOptions { allow_unclosed_class: true, ..spec_opts_unix_default() };
    let parsed = spec_parse_glob(seq!['{', '[', 'a', 'b', 'c', ',', '[', 'x', 'y', 'z', '}'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '(', '?', ':', '\\', '[', 'a', 'b', 'c', '|', '\\', '[', 'x', 'y', 'z', ')', '$']) by (compute);
}

// toregex!(allow_unclosed_class_brace3, "{[abc],[xyz}", ^(?:[abc]|\[xyz)$, UNCCLS)
proof fn ut_toregex_allow_unclosed_class_brace3() {
    let opts = GlobOptions { allow_unclosed_class: true, ..spec_opts_unix_default() };
    let parsed = spec_parse_glob(seq!['{', '[', 'a', 'b', 'c', ']', ',', '[', 'x', 'y', 'z', '}'], opts, false);
    let tokens = parsed.get_Ok_0();
    assert(spec_to_regex_with(opts, tokens, 64) == seq!['(', '?', '-', 'u', ')', '^', '(', '?', ':', '[', 'a', 'b', 'c', ']', '|', '\\', '[', 'x', 'y', 'z', ')', '$']) by (compute);
}


} // verus!

fn main() {}
